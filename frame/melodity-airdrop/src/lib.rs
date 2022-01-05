//! # Airdrop module
//! The module provides implementations for the bridge functionalities.
//!
//! - [`Config`](./trait.Config.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! This module provides functions to create one or more airdrop
//! released on demand by the airdrop controller

//! ### Module Functions
//!
//! - `createAirdrop` - create a new airdrop, can be run only by the controller origin
//! - `airdrop` - send the airdrop to the account, can be run only by the airdrop controller origin

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::unused_unit)]

use frame_support::debug;
use sp_std::convert::TryInto;
use frame_support::{
	ensure, pallet_prelude::*, Parameter,
	traits::{
		Currency, LockableCurrency, WithdrawReasons, ExistenceRequirement
	},
};
use sp_runtime::{
	traits::{
		CheckedAdd, CheckedSub, Zero, One, AtLeast128BitUnsigned
	},
	DispatchError,  
};
use sp_std::vec::Vec;
use frame_system::pallet_prelude::OriginFor;
use frame_system::{ensure_signed, Account};
// use pallet_balances::{Account, AccountData};

type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance; // <T as pallet_balances::Config>::Balance;
type Balance = u128;

/// Balance types where the airdrop will be sent.
#[derive(Encode, Decode, Clone, Copy, PartialEq, Eq, RuntimeDebug)]
pub enum AirdropTypes {
	/// Airdrop to the free balance.
	Free = 0,
	/// Airdrop to the reserved balance.
	Reserved = 1,
	/// Airdrop to the misc frozen balance.
	Frozen = 2,
	/// Airdrop to the fee frozen balance
	Fee = 3,
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct Airdrop<AirdropId, T: Config> {
	/// airdrop identifier
	pub id: AirdropId,
	/// airdrop name for quick identification
	pub name: Vec<u8>,
	/// url of the airdrop w/ description and more
	pub url: Vec<u8>,
	/// where the airdrop will be credited
	pub airdrop_type: AirdropTypes,
	/// amount of MELB the airdrop releases
	pub amount: BalanceOf<T>
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::config]
	pub trait Config: frame_system::Config + pallet_balances::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Required origin for making all the administrative modifications
		type ControllerOrigin: EnsureOrigin<Self::Origin>;

		/// Required origin for making all the airdrops
		type AirdropControllerOrigin: EnsureOrigin<Self::Origin>;

		/// The currency used.
		type Currency: Currency<Self::AccountId> + LockableCurrency<Self::AccountId>;
	}

	/// Error for non-fungible-token module.
	#[pallet::error]
	pub enum Error<T> {
		/// The required airdrop does not exists
		AirdropNotFound,
		/// No available airdrop id
		NoAvailableAirdropId,
		/// Numeric overflow
		Overflow,
		/// The required account does not exists
		AccountNotFound,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Airdrop successfully made \[account_id, airdrop_id, airdrop_amount\]
		Airdrop(T::AccountId, u128, BalanceOf<T>),
		/// New airdrop created successfully \[airdrop_id, airdrop_name\]
		CreatedAirdrop(u128, Vec<u8>),
	}

	pub type AirdropInfoOf<T> = Airdrop<u128, T>;

	/// Next available airdrop ID.
	#[pallet::storage]
	#[pallet::getter(fn next_airdrop_id)]
	pub type NextAirdropId<T: Config> = StorageValue<_, u128, ValueQuery>;

	/// Store the airdrop info.
	#[pallet::storage]
	#[pallet::getter(fn classes)]
	pub type Airdrops<T: Config> = StorageMap<_, Twox64Concat, u128, AirdropInfoOf<T>>;

	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Create a new airdrop
		#[pallet::weight(1_000_000_000)]
		pub fn createAirdrop(
			origin: OriginFor<T>,
			name: Vec<u8>,
			url: Vec<u8>,
			airdrop_type: AirdropTypes,
			amount: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			T::ControllerOrigin::ensure_origin(origin)?;

			let airdrop_id = NextAirdropId::<T>::try_mutate(|id| -> Result<u128, DispatchError> {
				let current_id = *id;
				*id = id.checked_add(1).ok_or(Error::<T>::NoAvailableAirdropId)?;
				Ok(current_id)
			})?;

			let info = Airdrop {
				id: airdrop_id,
				name: name.clone(),
				url,
				airdrop_type,
				amount,
			};
			Airdrops::<T>::insert(airdrop_id, info);

			// emit creation event
			Self::deposit_event(Event::CreatedAirdrop(airdrop_id, name));

			Ok(().into())
		}

		/// airdrop funds to the receiver account based on the airdrop identifier
		/// NOTE: the airdrop controller is responsible for avoiding multiple airdrops to the same account
		/// 	no data on the already sent airdrops are stored onchain
		#[pallet::weight(0)]
		pub fn airdrop(
			origin: OriginFor<T>,
			account: T::AccountId,
			airdrop_id: u128,
		) -> DispatchResultWithPostInfo {
			T::AirdropControllerOrigin::ensure_origin(origin)?;
			
			let airdrop = Airdrops::<T>::try_get(airdrop_id).or_else(|_| Err(Error::<T>::AirdropNotFound))?;

			match airdrop.airdrop_type {
				AirdropTypes::Free => Pallet::<T>::airdrop_to_free(airdrop_id, account.clone(), airdrop.amount),
				AirdropTypes::Reserved => Pallet::<T>::airdrop_to_reserved(airdrop_id, account.clone(), airdrop.amount),
				AirdropTypes::Frozen => Pallet::<T>::airdrop_to_frozen(airdrop_id, account.clone(), airdrop.amount),
				AirdropTypes::Fee => Pallet::<T>::airdrop_to_fee(airdrop_id, account.clone(), airdrop.amount),
			};

			// emit creation event
			Self::deposit_event(Event::Airdrop(account, airdrop_id, airdrop.amount));

			Ok(().into())
		}
	}
}

pub use pallet::*;

impl<T: Config> Pallet<T> {
	fn transform_u128_to_array_of_u8(x: u128) -> [u8; 8] {
		let b1: u8 = ((x >> 56) & 0xff) as u8;
		let b2: u8 = ((x >> 48) & 0xff) as u8;
		let b3: u8 = ((x >> 40) & 0xff) as u8;
		let b4: u8 = ((x >> 32) & 0xff) as u8;
		let b5: u8 = ((x >> 24) & 0xff) as u8;
		let b6: u8 = ((x >> 16) & 0xff) as u8;
		let b7: u8 = ((x >> 8) & 0xff) as u8;
		let b8: u8 = (x & 0xff) as u8;
		return [b1, b2, b3, b4, b5, b6, b7, b8]
	}

	/// Airdrop funds to fee wallet
	pub fn airdrop_to_fee(airdrop_id: u128, account: T::AccountId, amount: BalanceOf<T>) -> Result<(), DispatchError> {
		// lock funds
		// NOTE: funds locked are not cumulated, only the highest locked amount is kept
		T::Currency::extend_lock(
			Pallet::<T>::transform_u128_to_array_of_u8(airdrop_id), 
			&account, 
			amount, 
			WithdrawReasons::TRANSACTION_PAYMENT
		);
		// and release amount
		T::Currency::deposit_creating(&account, amount);

		Ok(().into())
	}

	/// Airdrop funds to reserved wallet
	pub fn airdrop_to_reserved(airdrop_id: u128, account: T::AccountId, amount: BalanceOf<T>) -> Result<(), DispatchError> {
		// lock funds
		// NOTE: funds locked are not cumulated, only the highest locked amount is kept
		T::Currency::extend_lock(
			Pallet::<T>::transform_u128_to_array_of_u8(airdrop_id), 
			&account, 
			amount, 
			WithdrawReasons::RESERVE
		);
		// and release amount
		T::Currency::deposit_creating(&account, amount);

		Ok(().into())
	}

	/// Airdrop funds to frozen wallet
	pub fn airdrop_to_frozen(airdrop_id: u128, account: T::AccountId, amount: BalanceOf<T>) -> Result<(), DispatchError> {
		// lock funds
		// NOTE: funds locked are not cumulated, only the highest locked amount is kept
		T::Currency::extend_lock(
			Pallet::<T>::transform_u128_to_array_of_u8(airdrop_id), 
			&account, 
			amount, 
			WithdrawReasons::FEE
		);
		// and release amount
		T::Currency::deposit_creating(&account, amount);

		Ok(().into())
	}

	/// Airdrop funds to free wallet
	pub fn airdrop_to_free(airdrop_id: u128, account: T::AccountId, amount: BalanceOf<T>) -> Result<(), DispatchError> {
		// release amount
		T::Currency::deposit_creating(&account, amount);

		Ok(().into())
	}
}