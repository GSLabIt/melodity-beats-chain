// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Scored Pool Module
//!
//! The module maintains a scored membership pool. Each entity in the
//! pool can be attributed a `Score`. From this pool a set `Members`
//! is constructed. This set contains the `MemberCount` highest
//! scoring entities. Unscored entities are never part of `Members`.
//!
//! If an entity wants to be part of the pool a deposit is required.
//! The deposit is returned when the entity withdraws or when it
//! is removed by an entity with the appropriate authority.
//!
//! Every `Period` blocks the set of `Members` is refreshed from the
//! highest scoring members in the pool and, no matter if changes
//! occurred, `T::MembershipChanged::set_members_sorted` is invoked.
//! On first load `T::MembershipInitialized::initialize_members` is
//! invoked with the initial `Members` set.
//!
//! It is possible to withdraw candidacy/resign your membership at any
//! time. If an entity is currently a member, this results in removal
//! from the `Pool` and `Members`; the entity is immediately replaced
//! by the next highest scoring candidate in the pool, if available.
//!
//! - [`scored_pool::Config`](./trait.Config.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Interface
//!
//! ### Public Functions
//!
//! - `submit_candidacy` - Submit candidacy to become a member. Requires a deposit.
//! - `withdraw_candidacy` - Withdraw candidacy. Deposit is returned.
//! - `score` - Attribute a quantitative score to an entity.
//! - `kick` - Remove an entity from the pool and members. Deposit is returned.
//! - `change_member_count` - Changes the amount of candidates taken into `Members`.
//!
//! ## Usage
//!
//! ```
//! use frame_support::{decl_module, dispatch};
//! use frame_system::ensure_signed;
//! use pallet_scored_pool::{self as scored_pool};
//!
//! pub trait Config: scored_pool::Config {}
//!
//! decl_module! {
//! 	pub struct Module<T: Config> for enum Call where origin: T::Origin {
//! 		#[weight = 0]
//! 		pub fn candidate(origin) -> dispatch::DispatchResult {
//! 			let who = ensure_signed(origin)?;
//!
//! 			let _ = <scored_pool::Module<T>>::submit_candidacy(
//! 				T::Origin::from(Some(who.clone()).into())
//! 			);
//! 			Ok(())
//! 		}
//! 	}
//! }
//!
//! # fn main() { }
//! ```
//!
//! ## Dependencies
//!
//! This module depends on the [System module](../frame_system/index.html).

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

use codec::{Codec, Encode, Decode, FullCodec};
use sp_std::{
	fmt::Debug,
	prelude::*,
};
use frame_support::{
	decl_module, decl_storage, decl_event, ensure, decl_error,
	traits::{
		EnsureOrigin, ChangeMembers, InitializeMembers, Currency, Get, ReservableCurrency, 
		WithdrawReasons, ExistenceRequirement, OnUnbalanced,
	},
	weights::Weight,
	pallet_prelude::{StorageDoubleMap, Twox64Concat, ValueQuery},
};
use frame_system::{ensure_root, ensure_signed};
use sp_runtime::traits::{AtLeast128BitUnsigned, MaybeSerializeDeserialize, Zero, StaticLookup};
use sp_runtime::{Percent, DispatchResult};
use sp_std::prelude::*;
use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;
use melodity_nft::NftExistance;
use sp_runtime::traits::CheckedAdd;

type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type PoolT<T> = Vec<((<T as frame_system::Config>::AccountId, u128), u128)>;
type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;

/// The enum is supplied when refreshing the members set.
/// Depending on the enum variant the corresponding associated
/// type function will be invoked.
enum ChangeReceiver {
	/// Should call `T::MembershipInitialized`.
	MembershipInitialized,
	/// Should call `T::MembershipChanged`.
	MembershipChanged,
}

pub trait Config: frame_system::Config {
	/// The currency used for deposits.
	type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>;

	/// The balance type of the the pool
	type Balance: Parameter + Member + AtLeast128BitUnsigned + Codec + Default + Copy +
		MaybeSerializeDeserialize + Debug;

	// The deposit which is reserved from candidates if they want to
	// start a candidacy. The deposit gets returned when the candidacy is
	// withdrawn or when the candidate is kicked.
	type CandidateDeposit: Get<BalanceOf<Self>>;

	/// Every `Period` blocks the `Members` are filled with the highest scoring
	/// members in the `Pool`.
	type Period: Get<Self::BlockNumber>;

	/// The receiver of the signal for when the membership has been initialized.
	/// This happens pre-genesis and will usually be the same as `MembershipChanged`.
	/// If you need to do something different on initialization, then you can change
	/// this accordingly.
	type MembershipInitialized: InitializeMembers<Self::AccountId>;

	/// The receiver of the signal for when the members have changed.
	type MembershipChanged: ChangeMembers<Self::AccountId>;

	/// Required origin for making all the administrative modifications
	type ControllerOrigin: EnsureOrigin<Self::Origin>;

	/// Percentage of the pool prize to reward to the first classified
	type FirstPrize: Get<Percent>;

	/// Percentage of the pool prize to reward to the second classified
	type SecondPrize: Get<Percent>;

	/// Percentage of the pool prize to reward to the third classified
	type ThirdPrize: Get<Percent>;

	/// Percentage of the pool prize to reward to the platform account
	type PlatformFee: Get<Percent>;

	/// Platform pot account where all the on-chain platform funds are stored
	type PlatformPot: Get<Self::AccountId>;

	/// Where the eventually remaining funds of the prize goes
	type RewardRemainder: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Instance of the melodity_nft pallet
	type Nft: NftExistance<u128, u128, Self::AccountId>;

	/// The prize given to the listener for the vote of a track
	/// The vector contains one or more tuples responsible for the prize handling
	/// Each tuple is constituted as follows:
	/// (
	/// 	number_of_tracks_participating_in_election,
	///		prize_given_to_artist_participanting_in_election,
	///		prize_given_to_listener_non_participating_in_election
	/// )
	type VoterPrize: Get<Vec<(u128, u128, u128)>>;

	/// The maximum prize a user can receive, this value is used to compute the
	/// prize as follows:
	///		max_prize = (number_of_tracks_participating_in_election + 1) * prize_limiter
	type PrizeLimiter: Get<u128>;
}

decl_storage! {
	trait Store for Module<T: Config> as ScoredPool {
		/// The current pool of candidates, stored as an ordered Vec
		/// (ordered descending by score, `None` last, highest first).
		Pool get(fn pool): PoolT<T>;

		/// A Map of the candidates. The information in this Map is redundant
		/// to the information in the `Pool`. But the Map enables us to easily
		/// check if a candidate is already in the pool, without having to
		/// iterate over the entire pool (the `Pool` is not sorted by
		/// `T::AccountId`, but by `T::Score` instead).
		CandidateExists get(fn candidate_exists): 
			double_map hasher(twox_64_concat) T::AccountId, hasher(twox_64_concat) u128 => bool;

		CandidateNumber get(fn candidate_number): u128;

		/// The current membership, stored as an ordered Vec.
		Members get(fn members): Vec<T::AccountId>;

		/// Size of the `Members` set.
		MemberCount get(fn member_count): u8;

		/// Pool prize
		PoolBalance get(fn pool_balance): BalanceOf<T>;

		/// A map of the addresses allowed to vote an nft (associated to an owner) participating to the election
		/// [voter, nft_owner, nft_id] => true
		CanVoteCandidate get(fn can_vote_candidate): 
			double_map hasher(twox_64_concat) T::AccountId, hasher(twox_64_concat) (T::AccountId, u128) => bool;
		
		/// Store the address of the user receiving the prize and the total prize already
		/// received
		GivenPrizes get(fn given_prizes): 
			map hasher(twox_64_concat) T::AccountId => u128;
	}
	add_extra_genesis {
		config(members): Vec<T::AccountId>;
		config(member_count): u8;
		build(|config| {})
	}
}

decl_event!(
	pub enum Event<T> where
		<T as frame_system::Config>::AccountId,
		Balance = BalanceOf<T>
	{
		/// An entity was just kicked out
		CandidateKicked,
		/// An entity has issued a candidacy. See the transaction for who.
		CandidateAdded,
		/// The candidacy was forcefully removed for an entity.
		/// See the transaction for who.
		/// \[sender, nft_owner, nft_id\]
		VoteEnabled(AccountId, AccountId, u128),
		/// A score was attributed to the candidate.
		/// See the transaction for who.
		/// \[nft_owner, nft_id\]
		CandidateScored(AccountId, u128),
		/// The prize distributed to the winner and the amount
		/// \[{first, prize}, {second, prize}, {third, prize}\]
		PrizeDistributed(
			Vec<(AccountId, Balance)>, 
			Vec<(AccountId, Balance)>,
			Vec<(AccountId, Balance)>
		),
	}
);

decl_error! {
	/// Error for the scored-pool module.
	pub enum Error for Module<T: Config> {
		/// Already a member.
		AlreadyInPool,
		/// Index out of bounds.
		InvalidIndex,
		/// Index does not match requested account.
		WrongAccountIndex,
		/// The maximum allowed pool prize was reached
		MaxPoolPrizeReached,
		/// The provided NFT identifier does not exists
		MissingNft,
		/// You are not the owner of the provided NFT
		NotOwnedNFT,
		/// The track has already reached the maximum score
		MaxScoreReached,
		/// Vote not yet enabled for this track
		VoteNotEnabled,
		/// Vote right already enabled for the pair (sender, (owner, id))
		VoteAlreadyEnabled,
		/// Vote already submitted for this track
		AlreadyVoted,
		/// Invalid score provided, it should be a number between 0 and 10 included
		ScoreNotValid,
		/// You cannot vote your own tracks
		UnableToVoteYourself,
		/// The maximum reachable prize overflows its limit
		MaximumReachablePrizeTooHigh,
	}
}

decl_module! {
	pub struct Module<T: Config>
		for enum Call
		where origin: T::Origin
	{
		type Error = Error<T>;

		fn deposit_event() = default;

		/// Every `Period` blocks the `Members` set is refreshed from the
		/// highest scoring members in the pool.
		fn on_initialize(n: T::BlockNumber) -> Weight {
			if n % T::Period::get() == Zero::zero() {
				let mut pool = <Pool<T>>::get();
				<Module<T>>::refresh_members(&pool, ChangeReceiver::MembershipChanged);
				let mut pool_balance = <PoolBalance<T>>::get();
				let first_prize: BalanceOf::<T> = T::FirstPrize::get().mul_floor(pool_balance);
				let second_prize: BalanceOf::<T> = T::SecondPrize::get().mul_floor(pool_balance);
				let third_prize: BalanceOf::<T> = T::ThirdPrize::get().mul_floor(pool_balance);
				let platform_fee: BalanceOf::<T> = T::PlatformFee::get().mul_floor(pool_balance);
				let mut remaining_funds: BalanceOf::<T> = pool_balance - platform_fee;
				
				let pool_length = pool.len();
				// handle edge cases where the the pool long enough
				match pool_length {
					// the pool is empty, no prize distribution exit immediately
					0 => {
						pool_balance = BalanceOf::<T>::zero();
						return 1000;
					},
					// one participant in the pool stop earlier, return all the the funds to
					// the participant
					1 => {
						T::Currency::deposit_creating(&pool[0].0.0, pool_balance);

						Self::deposit_event(Event::<T>::PrizeDistributed(
							vec![(pool[0].0.0.clone(), pool_balance)],
							vec![(pool[0].0.0.clone(), BalanceOf::<T>::zero())],
							vec![(pool[0].0.0.clone(), BalanceOf::<T>::zero())],
						));

						// empty the pool
						<CandidateExists<T>>::remove_all();
						<CanVoteCandidate<T>>::remove_all();
						<GivenPrizes<T>>::remove_all();
						CandidateNumber::put(0);
						pool.clear();
						<Pool<T>>::put(pool);
						pool_balance = BalanceOf::<T>::zero();
						<PoolBalance<T>>::put(pool_balance);

						return 500_000_000;
					},
					// two participants, use the standard prize division
					2 => {
						T::Currency::deposit_creating(&pool[0].0.0, first_prize);
						T::Currency::deposit_creating(&pool[1].0.0, second_prize);

						Self::deposit_event(Event::<T>::PrizeDistributed(
							vec![(pool[0].0.0.clone(), first_prize)],
							vec![(pool[1].0.0.clone(), second_prize)],
							vec![(pool[1].0.0.clone(), BalanceOf::<T>::zero())],
						));

						remaining_funds -= (first_prize + second_prize);
					},
					// distribute the prizes proportionally to the winners
					_ => {
						T::Currency::deposit_creating(&pool[0].0.0, first_prize);
						T::Currency::deposit_creating(&pool[1].0.0, second_prize);
						T::Currency::deposit_creating(&pool[2].0.0, third_prize);

						Self::deposit_event(Event::<T>::PrizeDistributed(
							vec![(pool[0].0.0.clone(), first_prize)],
							vec![(pool[1].0.0.clone(), second_prize)],
							vec![(pool[2].0.0.clone(), third_prize)],
						));

						remaining_funds -= (first_prize + second_prize + third_prize);
					}
				}

				// split the platform fee in 80% - 20%, the 20% will be destroied (implicitly burned)
				// while the other part will be taken as platform fee
				let deflate_platform_fee = platform_fee * 8u128.into() / 10u128.into();

				// deposit the platform fee to the platform pot account
				T::Currency::deposit_creating(&T::PlatformPot::get(), deflate_platform_fee);

				// split in half the 10% remaining, only 5% will be transferred to the treasury,
				// the remaining 5% will be destroied
				let deflate_remaining_funds = remaining_funds / 2u128.into();

				// store the remaining prize
				T::RewardRemainder::on_unbalanced(T::Currency::issue(deflate_remaining_funds));

				// finally reset the pool balance
				pool_balance = BalanceOf::<T>::zero();
				// empty the pool
				<CandidateExists<T>>::remove_all();
				<CanVoteCandidate<T>>::remove_all();
				<GivenPrizes<T>>::remove_all();
				CandidateNumber::put(0);
				pool.clear();
				<Pool<T>>::put(pool);
				<PoolBalance<T>>::put(pool_balance);
				return 1_000_000_000;
			}
			0
		}

		/// Add `origin` to the pool of candidates.
		/// This results in `CandidateDeposit` being withdrawn from
		/// the `origin` account. 
		///
		/// The dispatch origin of this function must be signed.
		///
		/// The `index` parameter of this function must be set to
		/// the index of the transactor in the `Pool`.
		#[weight = 1_000_000_000]
		pub fn submit_candidacy(origin, nft_id: u128) {
			let who = ensure_signed(origin)?;
			ensure!(!<CandidateExists<T>>::contains_key(&who, &nft_id), Error::<T>::AlreadyInPool);
			// check nft existance
			// MELT class id: 0
			ensure!(T::Nft::exists(0u128, nft_id), Error::<T>::MissingNft);
			// check nft ownance
			ensure!(T::Nft::owns(who.clone(), 0u128, nft_id), Error::<T>::NotOwnedNFT);

			let deposit = T::CandidateDeposit::get();
			// deflate the amount of funds actually stored in the prize, 90% is stored in the prize,
			// 10% is immediately destroied
			let deflated_deposit = deposit * 9u128.into() / 10u128.into();

			// check the origin can pay for the deposit
			//T::Currency::ensure_can_withdraw(&who, deposit, WithdrawReasons::TRANSACTION_PAYMENT)?;
			// pay the deposit
			T::Currency::withdraw(&who, deposit, WithdrawReasons::TRANSACTION_PAYMENT, ExistenceRequirement::KeepAlive)?;
			// add candidacy to pool prize
			let prize = <PoolBalance<T>>::get().checked_add(&deflated_deposit).ok_or(Error::<T>::MaxPoolPrizeReached)?;
			<PoolBalance<T>>::put(prize);

			// can be inserted as last element in pool, since entities with
			// `None` are always sorted to the end.
			<Pool<T>>::append(((who.clone(), nft_id.clone()), 0u128));

			<CandidateExists<T>>::insert(&who, &nft_id, true);

			// no checks are performed here as the number should already be locked by the max pool prize
			CandidateNumber::put(CandidateNumber::get() + 1);

			Self::deposit_event(RawEvent::CandidateAdded);
		}

		/// Kick a member `who` from the set.
		///
		/// May only be called from `T::KickOrigin`.
		///
		/// The `index` parameter of this function must be set to
		/// the index of `dest` in the `Pool`.
		#[weight = 1_000_000_000]
		pub fn kick(
			origin,
			dest: <T::Lookup as StaticLookup>::Source,
			nft_id: u128
		) {
			T::ControllerOrigin::ensure_origin(origin)?;

			let who = T::Lookup::lookup(dest)?;

			let pool = <Pool<T>>::get();

			// reduce the candidates number
			let candidates = CandidateNumber::get();
			if candidates > 0 {
				CandidateNumber::put(candidates - 1);
			}

			Self::remove_member(pool, who, nft_id)?;
			Self::deposit_event(RawEvent::CandidateKicked);
		}

		/// Grant the provided user the right to vote the pair of (nft_owner, nft_id)
		#[weight = 0]
		pub fn grant_vote_right(
			origin,
			dest: <T::Lookup as StaticLookup>::Source,
			nft_owner: <T::Lookup as StaticLookup>::Source,
			nft_id: u128
		) {
			T::ControllerOrigin::ensure_origin(origin)?;

			let voter = T::Lookup::lookup(dest)?;
			let owner = T::Lookup::lookup(nft_owner)?;

			// check nft existance
			ensure!(T::Nft::exists(0u128, nft_id), Error::<T>::MissingNft);
			
			// check nft ownance
			ensure!(T::Nft::owns(owner.clone(), 0u128, nft_id), Error::<T>::NotOwnedNFT);

			// the owner of the track cannot vote its own track
			ensure!(owner != voter, Error::<T>::UnableToVoteYourself);

			// check that the vote key not exists for the given track
			ensure!(!<CanVoteCandidate<T>>::contains_key(
				voter.clone(), 
				(owner.clone(), nft_id)
			), Error::<T>::VoteAlreadyEnabled);

			// update the map marking it as to vote
			<CanVoteCandidate<T>>::mutate(
				voter.clone(), 
				(owner.clone(), nft_id),
				|v| *v = true
			);

			Self::deposit_event(RawEvent::VoteEnabled(voter, owner, nft_id));
		}

		/// Score a member `who` with `score`.
		/// May only be called from `T::ScoreOrigin`.
		///
		/// The `index` parameter of this function must be set to
		/// the index of the `dest` in the `Pool`.
		/// 
		/// zero weight as it should be callable by anyone even without any balance
		#[weight = 1_000_000_000]
		pub fn score(
			origin,
			dest: <T::Lookup as StaticLookup>::Source,
			nft_id: u128,
			score: u128
		) {
			let sender = ensure_signed(origin)?;

			let who = T::Lookup::lookup(dest)?;
			
			// check that the vote key exists for the given track
			ensure!(<CanVoteCandidate<T>>::contains_key(
				sender.clone(), 
				(who.clone(), nft_id)
			), Error::<T>::VoteNotEnabled);

			// check that the user has not voted the track yet
			ensure!(<CanVoteCandidate<T>>::get(
				sender.clone(), 
				(who.clone(),nft_id)
			), Error::<T>::AlreadyVoted);

			// check that the vote is within the valid range
			ensure!(score >= 0u128 && score <= 10u128, Error::<T>::ScoreNotValid);

			let weighted_vote = match score {
				0 => 0b0u128,					// 0
				1 => 0b1u128,					// 1
				2 => 0b10u128,					// 2
				3 => 0b100u128,					// 4
				4 => 0b1000u128,				// 8
				5 => 0b10000u128,				// 16
				6 => 0b100000u128,				// 32
				7 => 0b1000000u128,				// 64
				8 => 0b10000000u128,			// 128
				9 => 0b100000000u128,			// 256
				10 => 0b1000000000u128,			// 512
				_ => 0b0u128
			};

			let mut pool = <Pool<T>>::get();
			let index = Self::index_of(&pool, who.clone(), nft_id.clone())?;
			//Self::ensure_index(&pool, &who, index)?;

			let new_score = weighted_vote.checked_add(pool[index].1).ok_or(Error::<T>::MaxScoreReached)?;

			// update the map marking it as already voted
			<CanVoteCandidate<T>>::mutate(
				sender.clone(), 
				(who.clone(),nft_id),
				|v| *v = false
			);

			// remove the record from the pool, it will be reinserted asap with the correct order
			pool.remove(index as usize);

			// we binary search the pool (which is sorted descending by score).
			// if there is already an element with `score`, we insert
			// right before that. if not, the search returns a location
			// where we can insert while maintaining order.
			let item = ((who.clone(), nft_id), new_score.clone());
			let location = pool
				.binary_search_by_key(
					&Reverse(new_score),
					|(_, maybe_score)| Reverse(*maybe_score)
				)
				.unwrap_or_else(|l| l);
			pool.insert(location, item);

			<Pool<T>>::put(&pool);

			// Compute the vote prize!
			let candidates = CandidateNumber::get();
			let tracks_in_election: u128 = (<CandidateExists<T>>::iter_prefix_values(sender.clone()).count() + 1) as u128;
			let maximum_prize = tracks_in_election.checked_mul(T::PrizeLimiter::get()).ok_or(Error::<T>::MaximumReachablePrizeTooHigh)?;
			let already_given_prize: u128 = if GivenPrizes::<T>::contains_key(sender.clone()) {
				<GivenPrizes<T>>::get(sender.clone())
			}
			else {
				0
			};
			let prize_tiers = T::VoterPrize::get();

			// if prize can still be given give the prize, otherwise no prize is given to the listener
			// no error occur as this is an allowed behaviour
			if already_given_prize < maximum_prize.into() {
				let mut prize_tier_index = 0;
				let mut next_prize_tier_index = prize_tier_index;


				while prize_tier_index < prize_tiers.len() -1 {
					next_prize_tier_index += 1;

					if candidates > prize_tiers[prize_tier_index].0 {
						prize_tier_index += 1;
						continue;
					}
					else if candidates < prize_tiers[prize_tier_index].0 {
						break;
					}
					else if next_prize_tier_index == prize_tiers.len() {
						// set the index to the last position of the prize_tiers vector
						prize_tier_index = prize_tiers.len() -1;
					}
				}

				let ending_prize = if tracks_in_election > 1 {
					prize_tiers[prize_tier_index].1
				} 
				else {
					prize_tiers[prize_tier_index].2
				};

				// the computed value should always leave in a safe range as an enormous amount of
				// funds is needed in order to let this cause an error
				if !GivenPrizes::<T>::contains_key(&sender) {
					GivenPrizes::<T>::insert(sender.clone(), ending_prize + already_given_prize)
				}
				else {
					GivenPrizes::<T>::try_mutate(sender.clone(), |value| -> DispatchResult {
						*value = ending_prize + already_given_prize;
						Ok(())
					});
				}

				// finally send the pool prize
				T::Currency::deposit_creating(&sender, ending_prize.into());
			}

			Self::deposit_event(RawEvent::CandidateScored(who, nft_id));
		}

		/// Dispatchable call to change `MemberCount`.
		///
		/// This will only have an effect the next time a refresh happens
		/// (this happens each `Period`).
		///
		/// May only be called from root.
		#[weight = 1_000_000_000]
		pub fn change_member_count(origin, count: u8) {
			T::ControllerOrigin::ensure_origin(origin)?;
			<MemberCount>::put(&count);
		}
	}
}

impl<T: Config> Module<T> {

	/// Fetches the `MemberCount` highest scoring members from
	/// `Pool` and puts them into `Members`.
	///
	/// The `notify` parameter is used to deduct which associated
	/// type function to invoke at the end of the method.
	fn refresh_members(
		pool: &PoolT<T>,
		notify: ChangeReceiver
	) {
		let count = <MemberCount>::get();

		let mut new_members: Vec<T::AccountId> = pool
			.into_iter()
			.filter(|(_, score)| score > &0u128)
			.take(count as usize)
			.map(|(account_id, _)| account_id.0.clone())
			.collect();
		new_members.sort();

		let old_members = <Members<T>>::get();
		<Members<T>>::put(&new_members);

		match notify {
			ChangeReceiver::MembershipInitialized =>
				T::MembershipInitialized::initialize_members(&new_members),
			ChangeReceiver::MembershipChanged =>
				T::MembershipChanged::set_members_sorted(
					&new_members[..],
					&old_members[..],
				),
		}
	}

	/// Removes an entity `remove` at `index` from the `Pool`.
	///
	/// If the entity is a member it is also removed from `Members` and
	/// the deposit is returned.
	fn remove_member(
		mut pool: PoolT<T>,
		remove: T::AccountId,
		nft_id: u128
	) -> Result<(), Error<T>> {
		// all callers of this function in this module also check
		// the index for validity before calling this function.
		// nevertheless we check again here, to assert that there was
		// no mistake when invoking this sensible function.
		let index = Self::index_of(&pool, remove.clone(), nft_id.clone())?;

		pool.remove(index as usize);
		<Pool<T>>::put(&pool);

		// remove from set, if it was in there
		let members = <Members<T>>::get();
		if members.binary_search(&remove).is_ok() {
			Self::refresh_members(&pool, ChangeReceiver::MembershipChanged);
		}

		<CandidateExists<T>>::remove(&remove, &nft_id);

		//T::Currency::unreserve(&remove, T::CandidateDeposit::get());

		Ok(())
	}

	fn index_of(pool: &PoolT<T>, who: T::AccountId, index: u128) -> Result<usize, Error<T>> {
		let mut res = pool.iter()
			.enumerate()
			.filter_map(|e| if e.1.0 == (who.clone(), index) { Some(e.0) } else { None });
		
		match res.next() {
			Some(val) => Ok(val),
			_ => Err(Error::<T>::MissingNft)
		}
	}
}