// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! The Substrate runtime. This can be compiled with `#[no_std]`, ready for Wasm.

#![cfg_attr(not(feature = "std"), no_std)]
// `construct_runtime!` does a lot of recursion and requires us to increase the limit to 256.
#![recursion_limit = "256"]

use sp_std::{marker::PhantomData};
use sp_std::prelude::*;
use frame_support::{
	construct_runtime, parameter_types, debug, RuntimeDebug, ConsensusEngineId,
	weights::{
		Weight, IdentityFee,
		constants::{BlockExecutionWeight, ExtrinsicBaseWeight, RocksDbWeight, WEIGHT_PER_SECOND}, DispatchClass,
	},
	traits::{
		Currency, Imbalance, KeyOwnerProofSystem, OnUnbalanced, Randomness, LockIdentifier,
		U128CurrencyToVote, Contains, FindAuthor
	},
};
use frame_system::{
	EnsureRoot, EnsureOneOf, EnsureSignedBy,
	limits::{BlockWeights, BlockLength}
};
use frame_support::traits::InstanceFilter;
use codec::{Encode, Decode};
use sp_core::{
	crypto::KeyTypeId,
	u32_trait::{_1, _2, _3, _4, _5},
	OpaqueMetadata,
};
pub use node_primitives::{AccountId, Signature};
use node_primitives::{AccountIndex, Balance, BlockNumber, Hash, Index, Moment};
use sp_api::impl_runtime_apis;
use sp_runtime::{
	Permill, Perbill, Perquintill, Percent, ApplyExtrinsicResult,
	impl_opaque_keys, generic, create_runtime_str, ModuleId, FixedPointNumber,
};
use sp_runtime::curve::PiecewiseLinear;
use sp_runtime::transaction_validity::{TransactionValidity, TransactionSource, TransactionPriority};
use sp_runtime::traits::{
	self, BlakeTwo256, Block as BlockT, StaticLookup, SaturatedConversion,
	ConvertInto, OpaqueKeys, NumberFor,
};
use sp_version::RuntimeVersion;
#[cfg(any(feature = "std", test))]
use sp_version::NativeVersion;
use pallet_grandpa::{AuthorityId as GrandpaId, AuthorityList as GrandpaAuthorityList};
use pallet_grandpa::fg_primitives;
use pallet_im_online::sr25519::AuthorityId as ImOnlineId;
use sp_authority_discovery::AuthorityId as AuthorityDiscoveryId;
use pallet_transaction_payment::{FeeDetails, RuntimeDispatchInfo};
pub use pallet_transaction_payment::{Multiplier, TargetedFeeAdjustment, CurrencyAdapter};
use pallet_session::{historical as pallet_session_historical};
use sp_inherents::{InherentData, CheckInherentsResult};
use static_assertions::const_assert;
use pallet_contracts::WeightInfo;
use hex_literal::hex;
use sp_core::crypto::Public;
use sp_core::{H160, H256, U256};
use fp_rpc::TransactionStatus;
use pallet_ethereum::{Call::transact, Transaction as EthereumTransaction};
use pallet_evm::{Account as EVMAccount, EnsureAddressTruncated, HashedAddressMapping, Runner};

#[cfg(any(feature = "std", test))]
pub use sp_runtime::BuildStorage;
#[cfg(any(feature = "std", test))]
pub use pallet_balances::Call as BalancesCall;
#[cfg(any(feature = "std", test))]
pub use frame_system::Call as SystemCall;
#[cfg(any(feature = "std", test))]
pub use pallet_staking::StakerStatus;

/// Implementations of some helper traits passed into runtime modules as associated types.
pub mod impls;
use impls::Author;

/// Constant values used within the runtime.
pub mod constants;
use constants::{time::*, currency::*};
use sp_runtime::generic::Era;

// Make the WASM binary available.
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

/// Wasm binary unwrapped. If built with `SKIP_WASM_BUILD`, the function panics.
#[cfg(feature = "std")]
pub fn wasm_binary_unwrap() -> &'static [u8] {
	WASM_BINARY.expect("Development wasm binary is not available. This means the client is \
						built with `SKIP_WASM_BUILD` flag and it is only usable for \
						production chains. Please rebuild with the flag disabled.")
}

/// Opaque types. These are used by the CLI to instantiate machinery that don't need to know
/// the specifics of the runtime. They can then be made to be agnostic over specific formats
/// of data like extrinsics, allowing for them to continue syncing the network through upgrades
/// to even the core data structures.
pub mod opaque {
	use super::*;

	pub use sp_runtime::OpaqueExtrinsic as UncheckedExtrinsic;

	/// Opaque block header type.
	pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
	/// Opaque block type.
	pub type Block = generic::Block<Header, UncheckedExtrinsic>;
	/// Opaque block identifier type.
	pub type BlockId = generic::BlockId<Block>;

	impl_opaque_keys! {
		pub struct SessionKeys {
			pub grandpa: Grandpa,
			pub babe: Babe,
			pub im_online: ImOnline,
			pub authority_discovery: AuthorityDiscovery,
		}
	}
}

/// Runtime version.
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: create_runtime_str!("melodity-beats"),
	impl_name: create_runtime_str!("virtuous-panda"),
	authoring_version: 1,
	// Per convention: if the runtime behavior changes, increment spec_version
	// and set impl_version to 0. If only runtime
	// implementation changes and behavior does not, then leave spec_version as
	// is and increment impl_version.
	spec_version: 105,
	impl_version: 1,
	apis: RUNTIME_API_VERSIONS,
	transaction_version: 1,
};

/// Native version.
#[cfg(any(feature = "std", test))]
pub fn native_version() -> NativeVersion {
	NativeVersion {
		runtime_version: VERSION,
		can_author_with: Default::default(),
	}
}

type NegativeImbalance = <Balances as Currency<AccountId>>::NegativeImbalance;
 
parameter_types! {
	/// Do Labs - Company address (root address)
	pub PlatformPot: AccountId = hex!["d6da31d2a7e66f26026263d66a4ca583f80f430197c25d00bc85f796813cca2b"].into();
	/// Derivation path: //airdrop//controller		[from company address]
	pub AirdropController: AccountId = hex!["0eceafe1c6ec459f38b55411f3974ac7c16fbed0e57d4c1189db6fb0cd23905e"].into();
	pub AirdropControllerVec: Vec<AccountId> = vec![AirdropController::get()];
	pub PlatformPotVec: Vec<AccountId> = vec![PlatformPot::get()];
}

impl Contains<AccountId> for PlatformPotVec {
	fn sorted_members() -> Vec<AccountId> {
		Self::get()
	}
	fn contains(t: &AccountId) -> bool {
		Self::get().contains(t)
	}
}

impl Contains<AccountId> for AirdropControllerVec {
	fn sorted_members() -> Vec<AccountId> {
		Self::get()
	}
	fn contains(t: &AccountId) -> bool {
		Self::get().contains(t)
	}
}

type EnsureAirdropControllerOr3OutOf4Council = EnsureOneOf<
	AccountId,
	EnsureSignedBy<AirdropControllerVec, AccountId>,
	pallet_collective::EnsureProportionMoreThan<_3, _4, AccountId, CouncilCollective>
>;

type EnsureRootOrHalfCouncil = EnsureOneOf<
	AccountId,
	EnsureRoot<AccountId>,
	pallet_collective::EnsureProportionMoreThan<_1, _2, AccountId, CouncilCollective>
>;

type EnsureRootOr3OutOf4Council = EnsureOneOf<
	AccountId,
	EnsureRoot<AccountId>,
	pallet_collective::EnsureProportionMoreThan<_3, _4, AccountId, CouncilCollective>
>;

type EnsureRootOr2OutOf3Council = EnsureOneOf<
	AccountId,
	EnsureRoot<AccountId>,
	pallet_collective::EnsureProportionMoreThan<_2, _3, AccountId, CouncilCollective>
>;

type EnsureRootOrFullCouncil = EnsureOneOf<
	AccountId,
	EnsureRoot<AccountId>,
	pallet_collective::EnsureProportionAtLeast<_1, _1, AccountId, CouncilCollective>
>;

type EnsureCompanyOrHalfCouncil = EnsureOneOf<
	AccountId,
	EnsureSignedBy<PlatformPotVec, AccountId>,
	pallet_collective::EnsureProportionMoreThan<_1, _2, AccountId, CouncilCollective>
>;

type EnsureHalfCouncil = pallet_collective::EnsureProportionMoreThan<_1, _2, AccountId, CouncilCollective>;
type Ensure3OutOf4Council = pallet_collective::EnsureProportionMoreThan<_3, _4, AccountId, CouncilCollective>;
type Ensure2OutOf3Council = pallet_collective::EnsureProportionMoreThan<_2, _3, AccountId, CouncilCollective>;
type EnsureFullCouncil = pallet_collective::EnsureProportionAtLeast<_1, _1, AccountId, CouncilCollective>;

pub struct DealWithFees;
impl OnUnbalanced<NegativeImbalance> for DealWithFees {
	fn on_unbalanceds<B>(mut fees_then_tips: impl Iterator<Item=NegativeImbalance>) {
		if let Some(fees) = fees_then_tips.next() {
			// for fees, 25% to treasury, 25% burn, 50% to split with platform and author
			let mut split = fees.ration(50, 50);
			if let Some(tips) = fees_then_tips.next() {
				// for tips, if any, 25% to treasury, 25% burn, 50% to split with platform and author
				tips.ration_merge_into(50, 50, &mut split);
			}

			// initial 50% is split in 25% and 25%
			let first_split = split.0.ration(50, 50);
			Treasury::on_unbalanced(first_split.0);
			Balances::burn(first_split.1.peek());

			// initial 50% is split in 10% and 40%
			let second_split = split.1.ration(20, 80);
			Balances::resolve_creating(&PlatformPot::get(), second_split.0);
			Author::on_unbalanced(second_split.1);
		}
	}
}

/// We assume that ~10% of the block weight is consumed by `on_initalize` handlers.
/// This is used to limit the maximal weight of a single extrinsic.
const AVERAGE_ON_INITIALIZE_RATIO: Perbill = Perbill::from_percent(10);
/// We allow `Normal` extrinsics to fill up the block up to 75%, the rest can be used
/// by  Operational  extrinsics.
const NORMAL_DISPATCH_RATIO: Perbill = Perbill::from_percent(75);
/// We allow for 2 seconds of compute with a 6 second average block time.
const MAXIMUM_BLOCK_WEIGHT: Weight = 2 * WEIGHT_PER_SECOND;

parameter_types! {
	pub const BlockHashCount: BlockNumber = 2400;
	pub const Version: RuntimeVersion = VERSION;
	pub RuntimeBlockLength: BlockLength =
		BlockLength::max_with_normal_ratio(5 * 1024 * 1024, NORMAL_DISPATCH_RATIO);
	pub RuntimeBlockWeights: BlockWeights = BlockWeights::builder()
		.base_block(BlockExecutionWeight::get())
		.for_class(DispatchClass::all(), |weights| {
			weights.base_extrinsic = ExtrinsicBaseWeight::get();
		})
		.for_class(DispatchClass::Normal, |weights| {
			weights.max_total = Some(NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT);
		})
		.for_class(DispatchClass::Operational, |weights| {
			weights.max_total = Some(MAXIMUM_BLOCK_WEIGHT);
			// Operational transactions have some extra reserved space, so that they
			// are included even if block reached `MAXIMUM_BLOCK_WEIGHT`.
			weights.reserved = Some(
				MAXIMUM_BLOCK_WEIGHT - NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT
			);
		})
		.avg_block_initialization(AVERAGE_ON_INITIALIZE_RATIO)
		.build_or_panic();
	pub const SS58Prefix: u8 = 57;
}

const_assert!(NORMAL_DISPATCH_RATIO.deconstruct() >= AVERAGE_ON_INITIALIZE_RATIO.deconstruct());

impl frame_system::Config for Runtime {
	type BaseCallFilter = ();
	type BlockWeights = RuntimeBlockWeights;
	type BlockLength = RuntimeBlockLength;
	type DbWeight = RocksDbWeight;
	type Origin = Origin;
	type Call = Call;
	type Index = Index;
	type BlockNumber = BlockNumber;
	type Hash = Hash;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = Indices;
	type Header = generic::Header<BlockNumber, BlakeTwo256>;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type Version = Version;
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = frame_system::weights::SubstrateWeight<Runtime>;
	type SS58Prefix = SS58Prefix;
}

impl pallet_utility::Config for Runtime {
	type Event = Event;
	type Call = Call;
	type WeightInfo = pallet_utility::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	// One storage item; key size is 32; value is size 4+4+16+32 bytes = 56 bytes.
	pub const DepositBase: Balance = deposit(1, 88);
	// Additional storage item size of 32 bytes.
	pub const DepositFactor: Balance = deposit(0, 32);
	pub const MaxSignatories: u16 = 100;
}

impl pallet_multisig::Config for Runtime {
	type Event = Event;
	type Call = Call;

	/// The currency mechanism.
	type Currency = Balances;

	/// The base amount of currency needed to reserve for creating a multisig execution or to store
	/// a dispatch call for later.
	///
	/// This is held for an additional storage item whose value size is
	/// `4 + sizeof((BlockNumber, Balance, AccountId))` bytes and whose key size is
	/// `32 + sizeof(AccountId)` bytes.
	type DepositBase = DepositBase;

	/// The amount of currency needed per unit threshold when creating a multisig execution.
	///
	/// This is held for adding 32 bytes more into a pre-existing storage value.
	type DepositFactor = DepositFactor;

	/// The maximum amount of signatories allowed in the multisig.
	type MaxSignatories = MaxSignatories;
	type WeightInfo = pallet_multisig::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	// One storage item; key size 32, value size 8; .
	pub const ProxyDepositBase: Balance = deposit(1, 8);
	// Additional storage item size of 33 bytes.
	pub const ProxyDepositFactor: Balance = deposit(0, 33);
	pub const MaxProxies: u16 = 32;
	pub const AnnouncementDepositBase: Balance = deposit(1, 8);
	pub const AnnouncementDepositFactor: Balance = deposit(0, 66);
	pub const MaxPending: u16 = 32;
}

/// The type used to represent the kinds of proxying allowed.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Encode, Decode, RuntimeDebug)]
pub enum ProxyType {
	Any,
	NonTransfer,
	Governance,
	Staking,
}
impl Default for ProxyType { fn default() -> Self { Self::Any } }
impl InstanceFilter<Call> for ProxyType {
	fn filter(&self, c: &Call) -> bool {
		match self {
			ProxyType::Any => true,
			ProxyType::NonTransfer => !matches!(
				c,
				Call::Balances(..) |
				// Call::Vesting(pallet_vesting::Call::vested_transfer(..)) |
				Call::Indices(pallet_indices::Call::transfer(..))
			),
			ProxyType::Governance => matches!(
				c,
				Call::Democracy(..) |
				Call::Council(..) |
				// Call::Society(..) |
				Call::TechnicalCommittee(..) |
				// Call::Elections(..) |
				Call::Treasury(..)
			),
			ProxyType::Staking => matches!(c, Call::Staking(..)),
		}
	}
	fn is_superset(&self, o: &Self) -> bool {
		match (self, o) {
			(x, y) if x == y => true,
			(ProxyType::Any, _) => true,
			(_, ProxyType::Any) => false,
			(ProxyType::NonTransfer, _) => true,
			_ => false,
		}
	}
}

impl pallet_proxy::Config for Runtime {
	type Event = Event;
	type Call = Call;
	type Currency = Balances;
	type ProxyType = ProxyType;
	type ProxyDepositBase = ProxyDepositBase;
	type ProxyDepositFactor = ProxyDepositFactor;
	type MaxProxies = MaxProxies;
	type WeightInfo = pallet_proxy::weights::SubstrateWeight<Runtime>;
	type MaxPending = MaxPending;
	type CallHasher = BlakeTwo256;
	type AnnouncementDepositBase = AnnouncementDepositBase;
	type AnnouncementDepositFactor = AnnouncementDepositFactor;
}

parameter_types! {
	pub MaximumSchedulerWeight: Weight = Perbill::from_percent(80) *
		RuntimeBlockWeights::get().max_block;
	pub const MaxScheduledPerBlock: u32 = 25;
}

impl pallet_scheduler::Config for Runtime {
	type Event = Event;
	type Origin = Origin;
	type PalletsOrigin = OriginCaller;
	type Call = Call;
	type MaximumWeight = MaximumSchedulerWeight;
	type ScheduleOrigin = EnsureRootOrHalfCouncil;
	type MaxScheduledPerBlock = MaxScheduledPerBlock;
	type WeightInfo = pallet_scheduler::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const EpochDuration: u64 = EPOCH_DURATION_IN_SLOTS;
	pub const ExpectedBlockTime: Moment = MILLISECS_PER_BLOCK;
	pub const ReportLongevity: u64 =
		BondingDuration::get() as u64 * SessionsPerEra::get() as u64 * EpochDuration::get();
}

impl pallet_babe::Config for Runtime {
	type EpochDuration = EpochDuration;
	type ExpectedBlockTime = ExpectedBlockTime;
	type EpochChangeTrigger = pallet_babe::ExternalTrigger;

	type KeyOwnerProofSystem = Historical;

	type KeyOwnerProof = <Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(
		KeyTypeId,
		pallet_babe::AuthorityId,
	)>>::Proof;

	type KeyOwnerIdentification = <Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(
		KeyTypeId,
		pallet_babe::AuthorityId,
	)>>::IdentificationTuple;

	type HandleEquivocation =
		pallet_babe::EquivocationHandler<Self::KeyOwnerIdentification, Offences, ReportLongevity>;

	type WeightInfo = ();
}

parameter_types! {
	pub const IndexDeposit: Balance = 1000 * DOLLARS;
}

impl pallet_indices::Config for Runtime {
	type AccountIndex = AccountIndex;
	type Currency = Balances;
	type Deposit = IndexDeposit;
	type Event = Event;
	type WeightInfo = pallet_indices::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const ExistentialDeposit: Balance = 0 * DOLLARS;
	// For weight estimation, we assume that the most locks on an individual account will be 50.
	// This number may need to be adjusted in the future if this assumption no longer holds true.
	pub const MaxLocks: u32 = 50;
}

impl pallet_balances::Config for Runtime {
	type MaxLocks = MaxLocks;
	type Balance = Balance;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = frame_system::Module<Runtime>; // AccountStore; 
	type WeightInfo = pallet_balances::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const TransactionByteFee: Balance = 1 * CENTS;
	pub const TargetBlockFullness: Perquintill = Perquintill::from_percent(25);
	pub AdjustmentVariable: Multiplier = Multiplier::saturating_from_rational(1, 100_000);
	pub MinimumMultiplier: Multiplier = Multiplier::saturating_from_rational(1, 1_000_000_000u128);
}

impl pallet_transaction_payment::Config for Runtime {
	/// Handler for withdrawing, refunding and depositing the transaction fee.
	/// Transaction fees are withdrawn before the transaction is executed.
	/// After the transaction was executed the transaction weight can be
	/// adjusted, depending on the used resources by the transaction. If the
	/// transaction weight is lower than expected, parts of the transaction fee
	/// might be refunded. In the end the fees can be deposited.
	type OnChargeTransaction = CurrencyAdapter<Balances, DealWithFees>;

	/// The fee to be paid for making a transaction; the per-byte portion.
	type TransactionByteFee = TransactionByteFee;

	/// Convert a weight value into a deductible fee based on the currency type.
	type WeightToFee = IdentityFee<Balance>;

	/// Update the multiplier of the next block, based on the previous block's weight.
	type FeeMultiplierUpdate =
		TargetedFeeAdjustment<Self, TargetBlockFullness, AdjustmentVariable, MinimumMultiplier>;
}

parameter_types! {
	pub const MinimumPeriod: Moment = SLOT_DURATION / 2;
}

impl pallet_timestamp::Config for Runtime {
	type Moment = Moment;
	type OnTimestampSet = Babe;
	type MinimumPeriod = MinimumPeriod;
	type WeightInfo = pallet_timestamp::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const UncleGenerations: BlockNumber = 5;
}

pub struct FindAuthorTruncated<F>(PhantomData<F>);
impl<F: FindAuthor<u32>> FindAuthor<H160> for FindAuthorTruncated<F> {
	fn find_author<'a, I>(digests: I) -> Option<H160>
	where
		I: 'a + IntoIterator<Item = (ConsensusEngineId, &'a [u8])>,
	{
		if let Some(author_index) = F::find_author(digests) {
			let authority_id = Babe::authorities()[author_index as usize].clone();
			return Some(H160::from_slice(&authority_id.0.to_raw_vec()[4..24]));
		}
		None
	}
}


impl pallet_authorship::Config for Runtime {
	type FindAuthor = pallet_session::FindAccountFromAuthorIndex<Self, Babe>;
	type UncleGenerations = UncleGenerations;
	type FilterUncle = ();
	type EventHandler = (Staking, ImOnline);
}

impl_opaque_keys! {
	pub struct SessionKeys {
		pub grandpa: Grandpa,
		pub babe: Babe,
		pub im_online: ImOnline,
		pub authority_discovery: AuthorityDiscovery,
	}
}

parameter_types! {
	pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(17);
}

impl pallet_session::Config for Runtime {
	type Event = Event;

	/// A stable ID for a validator.
	type ValidatorId = <Self as frame_system::Config>::AccountId;

	/// A conversion from account ID to validator ID.
	///
	/// Its cost must be at most one storage read.
	type ValidatorIdOf = pallet_staking::StashOf<Self>;

	/// Indicator for when to end the session.
	type ShouldEndSession = Babe;

	/// Something that can predict the next session rotation. This should typically come from the
	/// same logical unit that provides [`ShouldEndSession`], yet, it gives a best effort estimate.
	/// It is helpful to implement [`EstimateNextNewSession`].
	type NextSessionRotation = Babe;

	/// Handler for managing new session.
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Self, Staking>;

	/// Handler when a session has changed.
	type SessionHandler = <SessionKeys as OpaqueKeys>::KeyTypeIdProviders;

	/// The keys.
	type Keys = SessionKeys;

	/// The fraction of validators set that is safe to be disabled.
	///
	/// After the threshold is reached `disabled` method starts to return true,
	/// which in combination with `pallet_staking` forces a new era.
	type DisabledValidatorsThreshold = DisabledValidatorsThreshold;
	type WeightInfo = pallet_session::weights::SubstrateWeight<Runtime>;
}

impl pallet_session::historical::Config for Runtime {
	type FullIdentification = pallet_staking::Exposure<AccountId, Balance>;
	type FullIdentificationOf = pallet_staking::ExposureOf<Runtime>;
}

pallet_staking_reward_curve::build! {
	const REWARD_CURVE: PiecewiseLinear<'static> = curve!(
		min_inflation: 0_010_000,
		max_inflation: 0_020_000,
		ideal_stake: 0_500_000,
		falloff: 0_050_000,
		max_piece_count: 40,
		test_precision: 0_005_000,
	);
}

parameter_types! {
	pub const SessionsPerEra: sp_staking::SessionIndex = 6;
	pub const BondingDuration: pallet_staking::EraIndex = 24 * 28;
	pub const SlashDeferDuration: pallet_staking::EraIndex = 24 * 7; // 1/4 the bonding duration.
	pub const RewardCurve: &'static PiecewiseLinear<'static> = &REWARD_CURVE;
	pub const MaxNominatorRewardedPerValidator: u32 = 256;
	pub const ElectionLookahead: BlockNumber = EPOCH_DURATION_IN_BLOCKS / 4;
	pub const MaxIterations: u32 = 10;
	// 0.05%. The higher the value, the more strict solution acceptance becomes.
	pub MinSolutionScoreBump: Perbill = Perbill::from_rational_approximation(5u32, 10_000);
	pub OffchainSolutionWeightLimit: Weight = RuntimeBlockWeights::get()
		.get(DispatchClass::Normal)
		.max_extrinsic.expect("Normal extrinsics have a weight limit configured; qed")
		.saturating_sub(BlockExecutionWeight::get());
}

impl pallet_staking::Config for Runtime {
	type Currency = Balances;

	/// Time used for computing era duration.
	///
	/// It is guaranteed to start being called from the first `on_finalize`. Thus value at genesis
	/// is not used.
	type UnixTime = Timestamp;

	/// Convert a balance into a number used for election calculation. This must fit into a `u64`
	/// but is allowed to be sensibly lossy. The `u64` is used to communicate with the
	/// [`sp_npos_elections`] crate which accepts u64 numbers and does operations in 128.
	/// Consequently, the backward convert is used convert the u128s from sp-elections back to a
	/// [`BalanceOf`].
	type CurrencyToVote = U128CurrencyToVote;

	/// Tokens have been minted and are unused for validator-reward.
	/// See [Era payout](./index.html#era-payout).
	type RewardRemainder = Treasury;
	type Event = Event;

	/// Handler for the unbalanced reduction when slashing a staker.
	type Slash = Treasury; // send the slashed funds to the treasury.

	/// Handler for the unbalanced increment when rewarding a staker.
	type Reward = (); // rewards are minted from the void

	/// Number of sessions per era.
	type SessionsPerEra = SessionsPerEra;

	/// Number of eras that staked funds must remain bonded for.
	type BondingDuration = BondingDuration;

	/// Number of eras that slashes are deferred by, after computation.
	///
	/// This should be less than the bonding duration. Set to 0 if slashes
	/// should be applied immediately, without opportunity for intervention.
	type SlashDeferDuration = SlashDeferDuration;

	/// The origin which can cancel a deferred slash. Root can always do this.
	/// A super-majority of the council can cancel the slash.
	type SlashCancelOrigin = EnsureRootOr3OutOf4Council;

	/// Interface for interacting with a session pallet.
	type SessionInterface = Self;

	/// The NPoS reward curve used to define yearly inflation.
	/// See [Era payout](./index.html#era-payout).
	type RewardCurve = RewardCurve;

	/// Something that can estimate the next session change, accurately or as a best effort guess.
	type NextNewSession = Session;

	/// The number of blocks before the end of the era from which election submissions are allowed.
	///
	/// Setting this to zero will disable the offchain compute and only on-chain seq-phragmen will
	/// be used.
	///
	/// This is bounded by being within the last session. Hence, setting it to a value more than the
	/// length of a session will be pointless.
	type ElectionLookahead = ElectionLookahead;
	type Call = Call;

	/// Maximum number of balancing iterations to run in the offchain submission.
	///
	/// If set to 0, balance_solution will not be executed at all.
	type MaxIterations = MaxIterations;

	/// The threshold of improvement that should be provided for a new solution to be accepted.
	type MinSolutionScoreBump = MinSolutionScoreBump;

	/// The maximum number of nominators rewarded for each validator.
	///
	/// For each validator only the `$MaxNominatorRewardedPerValidator` biggest stakers can claim
	/// their reward. This used to limit the i/o cost for the nominator payout.
	type MaxNominatorRewardedPerValidator = MaxNominatorRewardedPerValidator;

	/// A configuration for base priority of unsigned transactions.
	///
	/// This is exposed so that it can be tuned for particular runtime, when
	/// multiple pallets send unsigned transactions.
	type UnsignedPriority = StakingUnsignedPriority;

	// The unsigned solution weight targeted by the OCW. We set it to the maximum possible value of
	// a single extrinsic.
	type OffchainSolutionWeightLimit = OffchainSolutionWeightLimit;
	type WeightInfo = pallet_staking::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const LaunchPeriod: BlockNumber = 10 * 24 * 60 * MINUTES;
	pub const VotingPeriod: BlockNumber = 10 * 24 * 60 * MINUTES;
	pub const FastTrackVotingPeriod: BlockNumber = 3 * 24 * 60 * MINUTES; // 1/3 VotingPeriod
	pub const InstantAllowed: bool = true;
	pub const MinimumDeposit: Balance = 1000 * DOLLARS;
	pub const EnactmentPeriod: BlockNumber = 30 * 24 * 60 * MINUTES;
	pub const CooloffPeriod: BlockNumber = 20 * 24 * 60 * MINUTES;
	// 10 cent: $100,000 / MB
	pub const PreimageByteDeposit: Balance = 10 * CENTS;
	pub const MaxVotes: u32 = 10;
	pub const MaxProposals: u32 = 10;
}

impl pallet_democracy::Config for Runtime {
	type Proposal = Call;
	type Event = Event;
	type Currency = Balances;

	/// The minimum period of locking and the period between a proposal being approved and enacted.
	///
	/// It should generally be a little more than the unstake period to ensure that
	/// voting stakers have an opportunity to remove themselves from the system in the case where
	/// they are on the losing side of a vote.
	type EnactmentPeriod = EnactmentPeriod;

	/// How often (in blocks) new public referenda are launched.
	type LaunchPeriod = LaunchPeriod;

	/// How often (in blocks) to check for new votes.
	type VotingPeriod = VotingPeriod;

	/// The minimum amount to be used as a deposit for a public referendum proposal.
	type MinimumDeposit = MinimumDeposit;

	/// Origin from which the next tabled referendum may be forced. This is a normal
	/// "super-majority-required" referendum.
	/// A straight majority of the council can decide what their next motion is.
	type ExternalOrigin = EnsureHalfCouncil;

	/// Origin from which the next tabled referendum may be forced; this allows for the tabling of
	/// a majority-carries referendum.
	/// A super-majority can have the next scheduled referendum be a straight majority-carries vote.
	type ExternalMajorityOrigin = Ensure3OutOf4Council;

	/// Origin from which the next tabled referendum may be forced; this allows for the tabling of
	/// a negative-turnout-bias (default-carries) referendum.
	/// A unanimous council can have the next scheduled referendum be a straight default-carries
	/// (NTB) vote.
	type ExternalDefaultOrigin = EnsureFullCouncil;

	/// Origin from which the next majority-carries (or more permissive) referendum may be tabled to
	/// vote according to the `FastTrackVotingPeriod` asynchronously in a similar manner to the
	/// emergency origin. It retains its threshold method.
	/// Two thirds of the technical committee can have an ExternalMajority/ExternalDefault vote
	/// be tabled immediately and with a shorter voting/enactment period.
	type FastTrackOrigin = Ensure2OutOf3Council;

	/// Origin from which the next majority-carries (or more permissive) referendum may be tabled to
	/// vote immediately and asynchronously in a similar manner to the emergency origin. It retains
	/// its threshold method.
	type InstantOrigin = EnsureFullCouncil;

	/// Indicator for whether an emergency origin is even allowed to happen. Some chains may want
	/// to set this permanently to `false`, others may want to condition it on things such as
	/// an upgrade having happened recently
	type InstantAllowed = InstantAllowed;

	/// Minimum voting period allowed for a fast-track referendum.
	type FastTrackVotingPeriod = FastTrackVotingPeriod;

	/// Origin from which any referendum may be cancelled in an emergency.
	/// To cancel a proposal which has been passed, 2/3 of the council must agree to it.
	type CancellationOrigin = Ensure2OutOf3Council;

	/// Origin from which a proposal may be cancelled and its backers slashed.
	/// To cancel a proposal before it has been passed, the council must be unanimous or
	/// Root must agree.
	type CancelProposalOrigin = EnsureFullCouncil;

	/// Origin from which proposals may be blacklisted.
	type BlacklistOrigin = EnsureFullCouncil;

	/// Origin for anyone able to veto proposals.
	///
	/// # Warning
	///
	/// The number of Vetoers for a proposal must be small, extrinsics are weighted according to
	/// [MAX_VETOERS](./const.MAX_VETOERS.html)
	/// Any single council member may veto a proposal, however they can
	/// only do it once and it lasts only for the cooloff period.
	type VetoOrigin = pallet_collective::EnsureMember<AccountId, CouncilCollective>;

	/// Period in blocks where an external proposal may not be re-submitted after being vetoed.
	type CooloffPeriod = CooloffPeriod;

	/// The amount of balance that must be deposited per byte of preimage stored.
	type PreimageByteDeposit = PreimageByteDeposit;

	/// An origin that can provide a preimage using operational extrinsics.
	type OperationalPreimageOrigin = pallet_collective::EnsureMember<AccountId, CouncilCollective>;

	/// Handler for the unbalanced reduction when slashing a preimage deposit.
	type Slash = Treasury;

	/// The Scheduler.
	type Scheduler = Scheduler;

	/// Overarching type of all pallets origins.
	type PalletsOrigin = OriginCaller;

	/// The maximum number of votes for an account.
	///
	/// Also used to compute weight, an overly big value can
	/// lead to extrinsic with very big weight: see `delegate` for instance.
	type MaxVotes = MaxVotes;

	type WeightInfo = pallet_democracy::weights::SubstrateWeight<Runtime>;

	/// The maximum number of public proposals that can exist at any time.
	type MaxProposals = MaxProposals;
}

parameter_types! {
	pub const CouncilMotionDuration: BlockNumber = 7 * DAYS;
	pub const CouncilMaxProposals: u32 = 10;
	pub const CouncilMaxMembers: u32 = 10;
}

type CouncilCollective = pallet_collective::Instance1;
impl pallet_collective::Config<CouncilCollective> for Runtime {
	type Origin = Origin;
	type Proposal = Call;
	type Event = Event;

	/// The time-out for council motions.
	type MotionDuration = CouncilMotionDuration;

	/// Maximum number of proposals allowed to be active in parallel.
	type MaxProposals = CouncilMaxProposals;

	/// The maximum number of members supported by the pallet. Used for weight estimation.
	///
	/// NOTE:
	/// + Benchmarks will need to be re-run and weights adjusted if this changes.
	/// + This pallet assumes that dependents keep to the limit without enforcing it.
	type MaxMembers = CouncilMaxMembers;

	/// Default vote strategy of this collective.
	type DefaultVote = pallet_collective::PrimeDefaultVote;
	type WeightInfo = pallet_collective::weights::SubstrateWeight<Runtime>;
}

// council members are elected by the council itself or by root
impl pallet_membership::Config<pallet_membership::Instance2> for Runtime {
	type Event = Event;

	/// Required origin for adding a member (though can always be Root).
	type AddOrigin = EnsureRootOrHalfCouncil;

	/// Required origin for removing a member (though can always be Root).
	type RemoveOrigin = EnsureHalfCouncil;

	/// Required origin for adding and removing a member in a single action.
	type SwapOrigin = EnsureHalfCouncil;

	/// Required origin for resetting membership.
	type ResetOrigin = Ensure3OutOf4Council;

	/// Required origin for setting or resetting the prime member.
	type PrimeOrigin = Ensure3OutOf4Council;

	/// The receiver of the signal for when the membership has been initialized. This happens pre-
	/// genesis and will usually be the same as `MembershipChanged`. If you need to do something
	/// different on initialization, then you can change this accordingly.
	type MembershipInitialized = Council;

	/// The receiver of the signal for when the membership has changed.
	type MembershipChanged = Council;
}

/* parameter_types! {
	pub const CandidacyBond: Balance = 1000 * DOLLARS;
	// 1 storage item created, key size is 32 bytes, value size is 16+16.
	pub const VotingBondBase: Balance = deposit(1, 64);
	// additional data per vote is 32 bytes (account id).
	pub const VotingBondFactor: Balance = deposit(0, 32);
	pub const TermDuration: BlockNumber = 0 * DAYS;	// passive mode
	pub const DesiredMembers: u32 = 13;
	pub const DesiredRunnersUp: u32 = 7;
	pub const ElectionsPhragmenModuleId: LockIdentifier = *b"phrelect";
}

// Make sure that there are no more than `MaxMembers` members elected via elections-phragmen.
const_assert!(DesiredMembers::get() <= CouncilMaxMembers::get());

impl pallet_elections_phragmen::Config for Runtime {
	type Event = Event;
	type ModuleId = ElectionsPhragmenModuleId;
	type Currency = Balances;

	/// What to do when the members change.
	type ChangeMembers = Council;

	/// What to do with genesis members
	// NOTE: this implies that council's genesis members cannot be set directly and must come from
	// this module.
	type InitializeMembers = Council;

	/// Convert a balance into a number used for election calculation.
	/// This must fit into a `u64` but is allowed to be sensibly lossy.
	type CurrencyToVote = U128CurrencyToVote;

	/// How much should be locked up in order to submit one's candidacy.
	type CandidacyBond = CandidacyBond;

	/// Base deposit associated with voting.
	///
	/// This should be sensibly high to economically ensure the pallet cannot be attacked by
	/// creating a gigantic number of votes.
	type VotingBondBase = VotingBondBase;

	/// The amount of bond that need to be locked for each vote (32 bytes).
	type VotingBondFactor = VotingBondFactor;

	/// Handler for the unbalanced reduction when a candidate has lost (and is not a runner-up)
	type LoserCandidate = ();

	/// Handler for the unbalanced reduction when a member has been kicked.
	type KickedMember = ();

	/// Number of members to elect.
	type DesiredMembers = DesiredMembers;

	/// Number of runners_up to keep.
	type DesiredRunnersUp = DesiredRunnersUp;

	/// How long each seat is kept. This defines the next block number at which an election
	/// round will happen. If set to zero, no elections are ever triggered and the module will
	/// be in passive mode.
	type TermDuration = TermDuration;
	type WeightInfo = pallet_elections_phragmen::weights::SubstrateWeight<Runtime>;
} */

parameter_types! {
	pub const TechnicalMotionDuration: BlockNumber = 7 * DAYS;
	pub const TechnicalMaxProposals: u32 = 10;
	pub const TechnicalMaxMembers: u32 = 25;
}

type TechnicalCollective = pallet_collective::Instance2;
impl pallet_collective::Config<TechnicalCollective> for Runtime {
	type Origin = Origin;
	type Proposal = Call;
	type Event = Event;

	/// The time-out for council motions.
	type MotionDuration = TechnicalMotionDuration;

	/// Maximum number of proposals allowed to be active in parallel.
	type MaxProposals = TechnicalMaxProposals;

	/// The maximum number of members supported by the pallet. Used for weight estimation.
	///
	/// NOTE:
	/// + Benchmarks will need to be re-run and weights adjusted if this changes.
	/// + This pallet assumes that dependents keep to the limit without enforcing it.
	type MaxMembers = TechnicalMaxMembers;

	/// Default vote strategy of this collective.
	type DefaultVote = pallet_collective::PrimeDefaultVote;
	type WeightInfo = pallet_collective::weights::SubstrateWeight<Runtime>;
}

impl pallet_membership::Config<pallet_membership::Instance1> for Runtime {
	type Event = Event;

	/// Required origin for adding a member (though can always be Root).
	type AddOrigin = EnsureRootOrHalfCouncil;

	/// Required origin for removing a member (though can always be Root).
	type RemoveOrigin = EnsureRootOrHalfCouncil;

	/// Required origin for adding and removing a member in a single action.
	type SwapOrigin = EnsureRootOrHalfCouncil;

	/// Required origin for resetting membership.
	type ResetOrigin = EnsureRootOrHalfCouncil;

	/// Required origin for setting or resetting the prime member.
	type PrimeOrigin = EnsureRootOrHalfCouncil;

	/// The receiver of the signal for when the membership has been initialized. This happens pre-
	/// genesis and will usually be the same as `MembershipChanged`. If you need to do something
	/// different on initialization, then you can change this accordingly.
	type MembershipInitialized = TechnicalCommittee;

	/// The receiver of the signal for when the membership has changed.
	type MembershipChanged = TechnicalCommittee;
}

parameter_types! {
	pub const ProposalBond: Permill = Permill::from_percent(10);
	pub const ProposalBondMinimum: Balance = 1000 * DOLLARS;
	pub const SpendPeriod: BlockNumber = 1 * DAYS;
	pub const Burn: Permill = Permill::from_percent(50);
	pub const TipCountdown: BlockNumber = 1 * DAYS;
	pub const TipFindersFee: Percent = Percent::from_percent(15);
	pub const TipReportDepositBase: Balance = 1000 * DOLLARS;
	pub const DataDepositPerByte: Balance = 10 * CENTS;
	pub const BountyDepositBase: Balance = 1000 * DOLLARS;
	pub const BountyDepositPayoutDelay: BlockNumber = 1 * DAYS;
	pub const TreasuryModuleId: ModuleId = ModuleId(*b"py/trsry");
	pub const BountyUpdatePeriod: BlockNumber = 28 * DAYS;
	pub const MaximumReasonLength: u32 = 16384;
	pub const BountyCuratorDeposit: Permill = Permill::from_percent(25);
	pub const BountyValueMinimum: Balance = 500 * DOLLARS;
}

impl pallet_treasury::Config for Runtime {
	/// The treasury's module id, used for deriving its sovereign account ID.
	type ModuleId = TreasuryModuleId;

	/// The staking balance.
	type Currency = Balances;

	/// Origin from which approvals must come.
	type ApproveOrigin = Ensure3OutOf4Council;

	/// Origin from which rejections must come.
	type RejectOrigin = EnsureHalfCouncil;
	type Event = Event;

	/// Handler for the unbalanced decrease when slashing for a rejected proposal or bounty.
	type OnSlash = ();

	/// Fraction of a proposal's value that should be bonded in order to place the proposal.
	/// An accepted proposal gets these back. A rejected proposal does not.
	type ProposalBond = ProposalBond;

	/// Minimum amount of funds that should be placed in a deposit for making a proposal.
	type ProposalBondMinimum = ProposalBondMinimum;

	/// Period between successive spends.
	type SpendPeriod = SpendPeriod;

	/// Percentage of spare funds (if any) that are burnt per spend period.
	type Burn = Burn;

	/// Handler for the unbalanced decrease when treasury funds are burned.
	type BurnDestination = ();

	/// Runtime hooks to external pallet using treasury to compute spend funds.
	type SpendFunds = Bounties;
	type WeightInfo = pallet_treasury::weights::SubstrateWeight<Runtime>;
}

impl pallet_bounties::Config for Runtime {
	type Event = Event;

	/// The amount held on deposit for placing a bounty proposal.
	type BountyDepositBase = BountyDepositBase;

	/// The delay period for which a bounty beneficiary need to wait before claim the payout.
	type BountyDepositPayoutDelay = BountyDepositPayoutDelay;

	/// Bounty duration in blocks.
	type BountyUpdatePeriod = BountyUpdatePeriod;

	/// Percentage of the curator fee that will be reserved upfront as deposit for bounty curator.
	type BountyCuratorDeposit = BountyCuratorDeposit;

	/// Minimum value for a bounty.
	type BountyValueMinimum = BountyValueMinimum;

	/// The amount held on deposit per byte within the tip report reason or bounty description.
	type DataDepositPerByte = DataDepositPerByte;

	/// Maximum acceptable reason length.
	type MaximumReasonLength = MaximumReasonLength;
	type WeightInfo = pallet_bounties::weights::SubstrateWeight<Runtime>;
}

/* impl pallet_tips::Config for Runtime {
	type Event = Event;

	/// The amount held on deposit per byte within the tip report reason or bounty description.
	type DataDepositPerByte = DataDepositPerByte;

	/// Maximum acceptable reason length.
	type MaximumReasonLength = MaximumReasonLength;

	/// Origin from which tippers must come.
	///
	/// `ContainsLengthBound::max_len` must be cost free (i.e. no storage read or heavy operation).
	type Tippers = Elections;

	/// The period for which a tip remains open after is has achieved threshold tippers.
	type TipCountdown = TipCountdown;

	/// The percent of the final tip which goes to the original reporter of the tip.
	type TipFindersFee = TipFindersFee;

	/// The amount held on deposit for placing a tip report.
	type TipReportDepositBase = TipReportDepositBase;
	type WeightInfo = pallet_tips::weights::SubstrateWeight<Runtime>;
} */

/* parameter_types! {
	pub const TombstoneDeposit: Balance = deposit(
		1,
		sp_std::mem::size_of::<pallet_contracts::ContractInfo<Runtime>>() as u32
	);
	pub const DepositPerContract: Balance = TombstoneDeposit::get();
	pub const DepositPerStorageByte: Balance = deposit(0, 1);
	pub const DepositPerStorageItem: Balance = deposit(1, 0);
	pub RentFraction: Perbill = Perbill::from_rational_approximation(1u32, 30 * DAYS);
	pub const SurchargeReward: Balance = 150 * MILLICENTS;
	pub const SignedClaimHandicap: u32 = 2;
	pub const MaxDepth: u32 = 32;
	pub const MaxValueSize: u32 = 16 * 1024;
	// The lazy deletion runs inside on_initialize.
	pub DeletionWeightLimit: Weight = AVERAGE_ON_INITIALIZE_RATIO *
		RuntimeBlockWeights::get().max_block;
	// The weight needed for decoding the queue should be less or equal than a fifth
	// of the overall weight dedicated to the lazy deletion.
	pub DeletionQueueDepth: u32 = ((DeletionWeightLimit::get() / (
			<Runtime as pallet_contracts::Config>::WeightInfo::on_initialize_per_queue_item(1) -
			<Runtime as pallet_contracts::Config>::WeightInfo::on_initialize_per_queue_item(0)
		)) / 5) as u32;
}

impl pallet_contracts::Config for Runtime {
	type Time = Timestamp;
	type Randomness = RandomnessCollectiveFlip;
	type Currency = Balances;
	type Event = Event;
	type RentPayment = ();
	type SignedClaimHandicap = SignedClaimHandicap;
	type TombstoneDeposit = TombstoneDeposit;
	type DepositPerContract = DepositPerContract;
	type DepositPerStorageByte = DepositPerStorageByte;
	type DepositPerStorageItem = DepositPerStorageItem;
	type RentFraction = RentFraction;
	type SurchargeReward = SurchargeReward;
	type MaxDepth = MaxDepth;
	type MaxValueSize = MaxValueSize;
	type WeightPrice = pallet_transaction_payment::Module<Self>;
	type WeightInfo = pallet_contracts::weights::SubstrateWeight<Self>;
	type ChainExtension = ();
	type DeletionQueueDepth = DeletionQueueDepth;
	type DeletionWeightLimit = DeletionWeightLimit;
} */

impl pallet_sudo::Config for Runtime {
	type Event = Event;
	type Call = Call;
}

parameter_types! {
	pub const SessionDuration: BlockNumber = EPOCH_DURATION_IN_SLOTS as _;
	pub const ImOnlineUnsignedPriority: TransactionPriority = TransactionPriority::max_value();
	/// We prioritize im-online heartbeats over election solution submission.
	pub const StakingUnsignedPriority: TransactionPriority = TransactionPriority::max_value() / 2;
}

impl<LocalCall> frame_system::offchain::CreateSignedTransaction<LocalCall> for Runtime
	where
		Call: From<LocalCall>,
{
	fn create_transaction<C: frame_system::offchain::AppCrypto<Self::Public, Self::Signature>>(
		call: Call,
		public: <Signature as traits::Verify>::Signer,
		account: AccountId,
		nonce: Index,
	) -> Option<(Call, <UncheckedExtrinsic as traits::Extrinsic>::SignaturePayload)> {
		let tip = 0;
		// take the biggest period possible.
		let period = BlockHashCount::get()
			.checked_next_power_of_two()
			.map(|c| c / 2)
			.unwrap_or(2) as u64;
		let current_block = System::block_number()
			.saturated_into::<u64>()
			// The `System::block_number` is initialized with `n+1`,
			// so the actual block number is `n`.
			.saturating_sub(1);
		let era = Era::mortal(period, current_block);
		let extra = (
			frame_system::CheckSpecVersion::<Runtime>::new(),
			frame_system::CheckTxVersion::<Runtime>::new(),
			frame_system::CheckGenesis::<Runtime>::new(),
			frame_system::CheckEra::<Runtime>::from(era),
			frame_system::CheckNonce::<Runtime>::from(nonce),
			frame_system::CheckWeight::<Runtime>::new(),
			pallet_transaction_payment::ChargeTransactionPayment::<Runtime>::from(tip),
		);
		let raw_payload = SignedPayload::new(call, extra)
			.map_err(|e| {
				debug::warn!("Unable to create signed payload: {:?}", e);
			})
			.ok()?;
		let signature = raw_payload
			.using_encoded(|payload| {
				C::sign(payload, public)
			})?;
		let address = Indices::unlookup(account);
		let (call, extra, _) = raw_payload.deconstruct();
		Some((call, (address, signature.into(), extra)))
	}
}

impl frame_system::offchain::SigningTypes for Runtime {
	type Public = <Signature as traits::Verify>::Signer;
	type Signature = Signature;
}

impl<C> frame_system::offchain::SendTransactionTypes<C> for Runtime where
	Call: From<C>,
{
	type Extrinsic = UncheckedExtrinsic;
	type OverarchingCall = Call;
}

impl pallet_im_online::Config for Runtime {
	type AuthorityId = ImOnlineId;
	type Event = Event;
	type ValidatorSet = Historical;
	type SessionDuration = SessionDuration;
	type ReportUnresponsiveness = Offences;
	type UnsignedPriority = ImOnlineUnsignedPriority;
	type WeightInfo = pallet_im_online::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub OffencesWeightSoftLimit: Weight = Perbill::from_percent(75) *
		RuntimeBlockWeights::get().max_block;
}

impl pallet_offences::Config for Runtime {
	type Event = Event;
	type IdentificationTuple = pallet_session::historical::IdentificationTuple<Self>;
	type OnOffenceHandler = Staking;
	type WeightSoftLimit = OffencesWeightSoftLimit;
}

impl pallet_authority_discovery::Config for Runtime {}

impl pallet_grandpa::Config for Runtime {
	type Event = Event;
	type Call = Call;

	type KeyOwnerProofSystem = Historical;

	type KeyOwnerProof =
		<Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(KeyTypeId, GrandpaId)>>::Proof;

	type KeyOwnerIdentification = <Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(
		KeyTypeId,
		GrandpaId,
	)>>::IdentificationTuple;

	type HandleEquivocation =
		pallet_grandpa::EquivocationHandler<Self::KeyOwnerIdentification, Offences, ReportLongevity>;

	type WeightInfo = ();
}

parameter_types! {
	pub CandidateDeposit: Balance = 1000 * DOLLARS;
	pub Period: BlockNumber = 7 * DAYS;
	pub FirstPrize: Percent = Percent::from_parts(40);
	pub SecondPrize: Percent = Percent::from_parts(25);
	pub ThirdPrize: Percent = Percent::from_parts(10);
	pub PlatformFee: Percent = Percent::from_parts(15);
	pub VoterPrize: Vec<(u128, Balance, Balance)> = vec![
		(10, 100 * DOLLARS, 10 * DOLLARS),
		(15, 90 * DOLLARS, 10 * DOLLARS),
		(20, 80 * DOLLARS, 10 * DOLLARS),
		(25, 70 * DOLLARS, 10 * DOLLARS),
		(30, 60 * DOLLARS, 10 * DOLLARS),
		(35, 50 * DOLLARS, 10 * DOLLARS),
		(40, 40 * DOLLARS, 10 * DOLLARS),
		(45, 30 * DOLLARS, 10 * DOLLARS),
		(u128::MAX, 20 * DOLLARS, 10 * DOLLARS),
	];
	pub PrizeLimiter: Balance = 1000 * DOLLARS;
}

impl melodity_track_election::Config for Runtime {
	/// The currency used for deposits.
	type Currency = Balances;

	/// The overarching event type.
	type Event = Event;

	/// The balance type of the the pool
	type Balance = Balance;

	// The deposit which is reserved from candidates if they want to
	// start a candidacy. The deposit gets returned when the candidacy is
	// withdrawn or when the candidate is kicked.
	type CandidateDeposit = CandidateDeposit;

	/// Every `Period` blocks the `Members` are filled with the highest scoring
	/// members in the `Pool`.
	type Period = Period;

	/// The receiver of the signal for when the membership has been initialized.
	/// This happens pre-genesis and will usually be the same as `MembershipChanged`.
	/// If you need to do something different on initialization, then you can change
	/// this accordingly.
	type MembershipInitialized = ();

	/// The receiver of the signal for when the members have changed.
	type MembershipChanged = ();

	/// Required origin for making all the administrative modifications
	type ControllerOrigin = EnsureCompanyOrHalfCouncil;

	/// Percentage of the pool prize to reward to the first classified
	type FirstPrize = FirstPrize;

	/// Percentage of the pool prize to reward to the second classified
	type SecondPrize = SecondPrize;

	/// Percentage of the pool prize to reward to the third classified
	type ThirdPrize = ThirdPrize;

	/// Percentage of the pool prize to reward to the platform account
	type PlatformFee = PlatformFee;

	/// Platform pot account where all the on-chain platform funds are stored
	type PlatformPot = PlatformPot;

	/// Where the eventually remaining funds of the prize goes
	type RewardRemainder = Treasury;

	/// Instance of the melodity_nft pallet
	type Nft = Nft;

	/// The prize given to the listener for the vote of a track
	/// The vector contains one or more tuples responsible for the prize handling
	/// Each tuple is constituted as follows:
	/// (
	/// 	number_of_tracks_participating_in_election,
	///		prize_given_to_artist_participanting_in_election,
	///		prize_given_to_listener_non_participating_in_election
	/// )
	type VoterPrize = VoterPrize;

	/// The maximum prize a user can receive, this value is used to compute the
	/// prize as follows:
	///		max_prize = (number_of_tracks_participating_in_election + 1) * prize_limiter
	type PrizeLimiter = PrizeLimiter;
}

parameter_types! {
	pub const BasicDeposit: Balance = 10 * DOLLARS;       // 258 bytes on-chain
	pub const FieldDeposit: Balance = 50 * CENTS;        // 66 bytes on-chain
	pub const SubAccountDeposit: Balance = 5 * DOLLARS;   // 53 bytes on-chain
	pub const MaxSubAccounts: u32 = 25;
	pub const MaxAdditionalFields: u32 = 100;
	pub const MaxRegistrars: u32 = 20;
}

impl pallet_identity::Config for Runtime {
	type Event = Event;
	type Currency = Balances;

	/// The amount held on deposit for a registered identity
	type BasicDeposit = BasicDeposit;

	/// The amount held on deposit per additional field for a registered identity.
	type FieldDeposit = FieldDeposit;

	/// The amount held on deposit for a registered subaccount. This should account for the fact
	/// that one storage item's value will increase by the size of an account ID, and there will be
	/// another trie item whose value is the size of an account ID plus 32 bytes.
	type SubAccountDeposit = SubAccountDeposit;

	/// The maximum number of sub-accounts allowed per identified account.
	type MaxSubAccounts = MaxSubAccounts;

	/// Maximum number of additional fields that may be stored in an ID. Needed to bound the I/O
	/// required to access an identity, but can be pretty high.
	type MaxAdditionalFields = MaxAdditionalFields;

	/// Maxmimum number of registrars allowed in the system. Needed to bound the complexity
	/// of, e.g., updating judgements.
	type MaxRegistrars = MaxRegistrars;

	/// What to do with slashed funds.
	type Slashed = Treasury;

	/// The origin which may forcibly set or remove a name. Root can always do this.
	type ForceOrigin = Ensure3OutOf4Council;

	/// The origin which may add or remove registrars. Root can always do this.
	type RegistrarOrigin = EnsureHalfCouncil;
	type WeightInfo = pallet_identity::weights::SubstrateWeight<Runtime>;
}

/* parameter_types! {
	pub const ConfigDepositBase: Balance = 5 * DOLLARS;
	pub const FriendDepositFactor: Balance = 50 * CENTS;
	pub const MaxFriends: u16 = 9;
	pub const RecoveryDeposit: Balance = 5 * DOLLARS;
}

impl pallet_recovery::Config for Runtime {
	type Event = Event;
	type Call = Call;
	type Currency = Balances;
	type ConfigDepositBase = ConfigDepositBase;
	type FriendDepositFactor = FriendDepositFactor;
	type MaxFriends = MaxFriends;
	type RecoveryDeposit = RecoveryDeposit;
} */

/* parameter_types! {
	pub const CandidateDeposit: Balance = 10 * DOLLARS;
	pub const WrongSideDeduction: Balance = 2 * DOLLARS;
	pub const MaxStrikes: u32 = 10;
	pub const RotationPeriod: BlockNumber = 80 * HOURS;
	pub const PeriodSpend: Balance = 500 * DOLLARS;
	pub const MaxLockDuration: BlockNumber = 36 * 30 * DAYS;
	pub const ChallengePeriod: BlockNumber = 7 * DAYS;
	pub const SocietyModuleId: ModuleId = ModuleId(*b"py/socie");
}

impl pallet_society::Config for Runtime {
	type Event = Event;
	type ModuleId = SocietyModuleId;
	type Currency = Balances;
	type Randomness = RandomnessCollectiveFlip;
	type CandidateDeposit = CandidateDeposit;
	type WrongSideDeduction = WrongSideDeduction;
	type MaxStrikes = MaxStrikes;
	type PeriodSpend = PeriodSpend;
	type MembershipChanged = ();
	type RotationPeriod = RotationPeriod;
	type MaxLockDuration = MaxLockDuration;
	type FounderSetOrigin = pallet_collective::EnsureProportionMoreThan<_1, _2, AccountId, CouncilCollective>;
	type SuspensionJudgementOrigin = pallet_society::EnsureFounder<Runtime>;
	type ChallengePeriod = ChallengePeriod;
} */

/* parameter_types! {
	pub const MinVestedTransfer: Balance = 100 * DOLLARS;
}

impl pallet_vesting::Config for Runtime {
	type Event = Event;
	type Currency = Balances;
	type BlockNumberToBalance = ConvertInto;
	type MinVestedTransfer = MinVestedTransfer;
	type WeightInfo = pallet_vesting::weights::SubstrateWeight<Runtime>;
} */

impl pallet_mmr::Config for Runtime {
	const INDEXING_PREFIX: &'static [u8] = b"mmr";
	type Hashing = <Runtime as frame_system::Config>::Hashing;
	type Hash = <Runtime as frame_system::Config>::Hash;
	type LeafData = frame_system::Module<Self>;
	type OnNewRoot = ();
	type WeightInfo = ();
}

parameter_types! {
	pub const LotteryModuleId: ModuleId = ModuleId(*b"py/lotto");
	pub const MaxCalls: usize = 5;
	pub const MaxGenerateRandom: u32 = 25;
}

/* impl pallet_lottery::Config for Runtime {
	type ModuleId = LotteryModuleId;
	type Call = Call;
	type Event = Event;
	type Currency = Balances;

	/// Something that provides randomness in the runtime.
	type Randomness = RandomnessCollectiveFlip;

	/// The manager origin.
	type ManagerOrigin = EnsureRootOrHalfCouncil;

	/// The max number of calls available in a single lottery.
	type MaxCalls = MaxCalls;

	/// Used to determine if a call would be valid for purchasing a ticket.
	///
	/// Be conscious of the implementation used here. We assume at worst that
	/// a vector of `MaxCalls` indices are queried for any call validation.
	/// You may need to provide a custom benchmark if this assumption is broken.
	type ValidateCall = Lottery;

	/// Number of time we should try to generate a random number that has no modulo bias.
	/// The larger this number, the more potential computation is used for picking the winner,
	/// but also the more likely that the chosen winner is done fairly.
	type MaxGenerateRandom = MaxGenerateRandom;
	type WeightInfo = pallet_lottery::weights::SubstrateWeight<Runtime>;
} */

parameter_types! {
	pub const AssetDepositBase: Balance = 1000 * DOLLARS;
	pub const AssetDepositPerZombie: Balance = 1 * DOLLARS;
	pub const StringLimit: u32 = 50;
	pub const MetadataDepositBase: Balance = 10 * DOLLARS;
	pub const MetadataDepositPerByte: Balance = 50 * CENTS;
}

impl pallet_assets::Config for Runtime {
	type Event = Event;
	type Balance = Balance;
	type AssetId = u32;
	type Currency = Balances;

	/// The origin which may forcibly create or destroy an asset or otherwise alter privileged
	/// attributes.
	type ForceOrigin = Ensure3OutOf4Council;

	/// The basic amount of funds that must be reserved when creating a new asset class.
	type AssetDepositBase = AssetDepositBase;

	/// The additional funds that must be reserved for every zombie account that an asset class
	/// supports.
	type AssetDepositPerZombie = AssetDepositPerZombie;

	/// The maximum length of a name or symbol stored on-chain.
	type StringLimit = StringLimit;

	/// The basic amount of funds that must be reserved when adding metadata to your asset.
	type MetadataDepositBase = MetadataDepositBase;

	/// The additional funds that must be reserved for the number of bytes you store in your
	/// metadata.
	type MetadataDepositPerByte = MetadataDepositPerByte;
	type WeightInfo = pallet_assets::weights::SubstrateWeight<Runtime>;
}

impl melodity_nft::Config for Runtime {
	type Event = Event;

	/// The class ID type
	type ClassId = u128;

	/// The token ID type
	type TokenId = u128;

	/// The class properties type
	type ClassData = Vec<u8>;

	/// The token properties type
	type TokenData = melodity_nft::MelodityNFTData;

	/// Required origin for making all the administrative modifications
	type ControllerOrigin = EnsureHalfCouncil;

	/// The currency used for fee payment.
	type Currency = Balances;
}

parameter_types! {
	pub const FeeDecimalPositions: Balance = 100_000_000;
}

impl melodity_bridge::Config for Runtime {
	type Event = Event;

	/// Required origin for making all the administrative modifications
	type ControllerOrigin = Ensure2OutOf3Council;

	/// The currency used for fee payment.
	type Currency = Balances;

	/// The address where the conversion fee will be deposited
	type PlatformPot = PlatformPot;

	/// The number of decimal positions for the fee definition
	type FeeDecimalPositions = FeeDecimalPositions;	// 8
}

impl melodity_airdrop::Config for Runtime {
	type Event = Event;

	/// Required origin for making all the administrative modifications
	type ControllerOrigin = EnsureRootOrHalfCouncil;

	/// The currency used for fee payment.
	type AirdropControllerOrigin = EnsureAirdropControllerOr3OutOf4Council;

	/// The address where the conversion fee will be deposited
	type Currency = Balances;
}

parameter_types! {
	pub const ChainId: u64 = 57;
	pub BlockGasLimit: U256 = U256::from(u32::max_value());
}

impl pallet_evm::Config for Runtime {
	type Event = Event;

	// Calculator for current gas price.
	type FeeCalculator = pallet_dynamic_fee::Module<Self>;

	/// Maps Ethereum gas to Substrate weight.
	type GasWeightMapping = ();

	/// Block number to block hash.
	type BlockHashMapping = pallet_ethereum::EthereumBlockHashMapping;

	/// Allow the origin to call on behalf of given address.
	type CallOrigin = EnsureAddressTruncated;

	/// Allow the origin to withdraw on behalf of given address.
	type WithdrawOrigin = EnsureAddressTruncated;

	/// Mapping from address to account id.
	type AddressMapping = HashedAddressMapping<BlakeTwo256>;

	/// Currency type for withdraw and balance storage.
	type Currency = Balances;

	/// EVM execution runner.
	type Runner = pallet_evm::runner::stack::Runner<Self>;

	/// Precompiles associated with this EVM engine.
	type Precompiles = (
		pallet_evm_precompile_simple::ECRecover,
		pallet_evm_precompile_simple::Sha256,
		pallet_evm_precompile_simple::Ripemd160,
		pallet_evm_precompile_simple::Identity,
		pallet_evm_precompile_modexp::Modexp,
		pallet_evm_precompile_simple::ECRecoverPublicKey,
		pallet_evm_precompile_sha3fips::Sha3FIPS256,
		pallet_evm_precompile_sha3fips::Sha3FIPS512,
	);

	/// Chain ID of EVM.
	type ChainId = ChainId;

	/// The block gas limit. Can be a simple constant, or an adjustment algorithm in another pallet.
	type BlockGasLimit = BlockGasLimit;

	/// To handle fee deduction for EVM transactions. An example is this pallet being used by `pallet_ethereum`
	/// where the chain implementing `pallet_ethereum` should be able to configure what happens to the fees
	/// Similar to `OnChargeTransaction` of `pallet_transaction_payment`
	type OnChargeTransaction = ();

	/// Find author for the current block.
	type FindAuthor = FindAuthorTruncated<Babe>; // pallet_session::FindAccountFromAuthorIndex<Self, Babe>;
}

impl pallet_ethereum::Config for Runtime {
	type Event = Event;

	/// How Ethereum state root is calculated.
	type StateRoot = pallet_ethereum::IntermediateStateRoot;
}

frame_support::parameter_types! {
	pub BoundDivision: U256 = U256::from(1024);
}

impl pallet_dynamic_fee::Config for Runtime {
	/// Bound divisor for min gas price.
	type MinGasPriceBoundDivisor = BoundDivision;
}

construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = node_primitives::Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system::{Module, Call, Config, Storage, Event<T>},
		Utility: pallet_utility::{Module, Call, Event},
		Babe: pallet_babe::{Module, Call, Storage, Config, Inherent, ValidateUnsigned},
		Timestamp: pallet_timestamp::{Module, Call, Storage, Inherent},
		Authorship: pallet_authorship::{Module, Call, Storage, Inherent},
		Indices: pallet_indices::{Module, Call, Storage, Config<T>, Event<T>},
		Balances: pallet_balances::{Module, Call, Storage, Config<T>, Event<T>},
		TransactionPayment: pallet_transaction_payment::{Module, Storage},
		Staking: pallet_staking::{Module, Call, Config<T>, Storage, Event<T>, ValidateUnsigned},
		Session: pallet_session::{Module, Call, Storage, Event, Config<T>},
		Democracy: pallet_democracy::{Module, Call, Storage, Config, Event<T>},
		Council: pallet_collective::<Instance1>::{Module, Call, Storage, Origin<T>, Event<T>, Config<T>},
		CouncilMembership: pallet_membership::<Instance2>::{Module, Call, Storage, Event<T>, Config<T>},
		TechnicalCommittee: pallet_collective::<Instance2>::{Module, Call, Storage, Origin<T>, Event<T>, Config<T>},
		// Elections: pallet_elections_phragmen::{Module, Call, Storage, Event<T>, Config<T>},
		TechnicalMembership: pallet_membership::<Instance1>::{Module, Call, Storage, Event<T>, Config<T>},
		Grandpa: pallet_grandpa::{Module, Call, Storage, Config, Event, ValidateUnsigned},
		Treasury: pallet_treasury::{Module, Call, Storage, Config, Event<T>},
		// Contracts: pallet_contracts::{Module, Call, Config<T>, Storage, Event<T>},
		Sudo: pallet_sudo::{Module, Call, Config<T>, Storage, Event<T>},
		ImOnline: pallet_im_online::{Module, Call, Storage, Event<T>, ValidateUnsigned, Config<T>},
		AuthorityDiscovery: pallet_authority_discovery::{Module, Call, Config},
		Offences: pallet_offences::{Module, Call, Storage, Event},
		Historical: pallet_session_historical::{Module},
		RandomnessCollectiveFlip: pallet_randomness_collective_flip::{Module, Call, Storage},
		Identity: pallet_identity::{Module, Call, Storage, Event<T>},
		// Society: pallet_society::{Module, Call, Storage, Event<T>, Config<T>},
		// Recovery: pallet_recovery::{Module, Call, Storage, Event<T>},
		// Vesting: pallet_vesting::{Module, Call, Storage, Event<T>, Config<T>},
		Scheduler: pallet_scheduler::{Module, Call, Storage, Event<T>},
		Proxy: pallet_proxy::{Module, Call, Storage, Event<T>},
		Multisig: pallet_multisig::{Module, Call, Storage, Event<T>},
		Bounties: pallet_bounties::{Module, Call, Storage, Event<T>},
		// Tips: pallet_tips::{Module, Call, Storage, Event<T>},
		Assets: pallet_assets::{Module, Call, Storage, Event<T>},
		Mmr: pallet_mmr::{Module, Storage},
		// Lottery: pallet_lottery::{Module, Call, Storage, Event<T>},

		Nft: melodity_nft::{Module, Call, Storage, Event<T>, Config<T>},
		TrackElection: melodity_track_election::{Module, Call, Storage, Event<T>, Config<T>},
		Bridge: melodity_bridge::{Module, Call, Storage, Event<T>, Config},
		Airdrop: melodity_airdrop::{Module, Call, Storage, Event<T>},

		// frontier
		Ethereum: pallet_ethereum::{Module, Call, Storage, Event, Config, ValidateUnsigned},
		Evm: pallet_evm::{Module, Config, Call, Storage, Event<T>},
		DynamicFee: pallet_dynamic_fee::{Module, Call, Storage, Config, Inherent},
	}
);

pub struct TransactionConverter;

impl fp_rpc::ConvertTransaction<UncheckedExtrinsic> for TransactionConverter {
	fn convert_transaction(&self, transaction: pallet_ethereum::Transaction) -> UncheckedExtrinsic {
		UncheckedExtrinsic::new_unsigned(
			pallet_ethereum::Call::<Runtime>::transact(transaction).into(),
		)
	}
}

impl fp_rpc::ConvertTransaction<opaque::UncheckedExtrinsic> for TransactionConverter {
	fn convert_transaction(
		&self,
		transaction: pallet_ethereum::Transaction,
	) -> opaque::UncheckedExtrinsic {
		let extrinsic = UncheckedExtrinsic::new_unsigned(
			pallet_ethereum::Call::<Runtime>::transact(transaction).into(),
		);
		let encoded = extrinsic.encode();
		opaque::UncheckedExtrinsic::decode(&mut &encoded[..])
			.expect("Encoded extrinsic is always valid")
	}
}

/// The address format for describing accounts.
pub type Address = sp_runtime::MultiAddress<AccountId, AccountIndex>;
/// Block header type as expected by this runtime.
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
/// Block type as expected by this runtime.
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
/// A Block signed with a Justification
pub type SignedBlock = generic::SignedBlock<Block>;
/// BlockId type as expected by this runtime.
pub type BlockId = generic::BlockId<Block>;
/// The SignedExtension to the basic transaction logic.
///
/// When you change this, you **MUST** modify [`sign`] in `bin/node/testing/src/keyring.rs`!
///
/// [`sign`]: <../../testing/src/keyring.rs.html>
pub type SignedExtra = (
	frame_system::CheckSpecVersion<Runtime>,
	frame_system::CheckTxVersion<Runtime>,
	frame_system::CheckGenesis<Runtime>,
	frame_system::CheckEra<Runtime>,
	frame_system::CheckNonce<Runtime>,
	frame_system::CheckWeight<Runtime>,
	pallet_transaction_payment::ChargeTransactionPayment<Runtime>,
);
/// Unchecked extrinsic type as expected by this runtime.
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<Address, Call, Signature, SignedExtra>;
/// The payload being signed in transactions.
pub type SignedPayload = generic::SignedPayload<Call, SignedExtra>;
/// Extrinsic type that has already been checked.
pub type CheckedExtrinsic = generic::CheckedExtrinsic<AccountId, Call, SignedExtra>;
/// Executive: handles dispatch to the various modules.
pub type Executive = frame_executive::Executive<Runtime, Block, frame_system::ChainContext<Runtime>, Runtime, AllModules>;

/// MMR helper types.
mod mmr {
	use super::Runtime;
	pub use pallet_mmr::primitives::*;

	pub type Leaf = <
		<Runtime as pallet_mmr::Config>::LeafData
		as
		LeafDataProvider
	>::LeafData;
	pub type Hash = <Runtime as pallet_mmr::Config>::Hash;
	pub type Hashing = <Runtime as pallet_mmr::Config>::Hashing;
}

impl_runtime_apis! {
	impl sp_api::Core<Block> for Runtime {
		fn version() -> RuntimeVersion {
			VERSION
		}

		fn execute_block(block: Block) {
			Executive::execute_block(block)
		}

		fn initialize_block(header: &<Block as BlockT>::Header) {
			Executive::initialize_block(header)
		}
	}

	impl sp_api::Metadata<Block> for Runtime {
		fn metadata() -> OpaqueMetadata {
			Runtime::metadata().into()
		}
	}

	impl sp_block_builder::BlockBuilder<Block> for Runtime {
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyExtrinsicResult {
			Executive::apply_extrinsic(extrinsic)
		}

		fn finalize_block() -> <Block as BlockT>::Header {
			Executive::finalize_block()
		}

		fn inherent_extrinsics(data: InherentData) -> Vec<<Block as BlockT>::Extrinsic> {
			data.create_extrinsics()
		}

		fn check_inherents(block: Block, data: InherentData) -> CheckInherentsResult {
			data.check_extrinsics(&block)
		}

		fn random_seed() -> <Block as BlockT>::Hash {
			RandomnessCollectiveFlip::random_seed()
		}
	}

	impl sp_transaction_pool::runtime_api::TaggedTransactionQueue<Block> for Runtime {
		fn validate_transaction(
			source: TransactionSource,
			tx: <Block as BlockT>::Extrinsic,
		) -> TransactionValidity {
			Executive::validate_transaction(source, tx)
		}
	}

	impl sp_offchain::OffchainWorkerApi<Block> for Runtime {
		fn offchain_worker(header: &<Block as BlockT>::Header) {
			Executive::offchain_worker(header)
		}
	}

	impl fg_primitives::GrandpaApi<Block> for Runtime {
		fn grandpa_authorities() -> GrandpaAuthorityList {
			Grandpa::grandpa_authorities()
		}

		fn submit_report_equivocation_unsigned_extrinsic(
			equivocation_proof: fg_primitives::EquivocationProof<
				<Block as BlockT>::Hash,
				NumberFor<Block>,
			>,
			key_owner_proof: fg_primitives::OpaqueKeyOwnershipProof,
		) -> Option<()> {
			let key_owner_proof = key_owner_proof.decode()?;

			Grandpa::submit_unsigned_equivocation_report(
				equivocation_proof,
				key_owner_proof,
			)
		}

		fn generate_key_ownership_proof(
			_set_id: fg_primitives::SetId,
			authority_id: GrandpaId,
		) -> Option<fg_primitives::OpaqueKeyOwnershipProof> {
			use codec::Encode;

			Historical::prove((fg_primitives::KEY_TYPE, authority_id))
				.map(|p| p.encode())
				.map(fg_primitives::OpaqueKeyOwnershipProof::new)
		}
	}

	impl sp_consensus_babe::BabeApi<Block> for Runtime {
		fn configuration() -> sp_consensus_babe::BabeGenesisConfiguration {
			// The choice of `c` parameter (where `1 - c` represents the
			// probability of a slot being empty), is done in accordance to the
			// slot duration and expected target block time, for safely
			// resisting network delays of maximum two seconds.
			// <https://research.web3.foundation/en/latest/polkadot/BABE/Babe/#6-practical-results>
			sp_consensus_babe::BabeGenesisConfiguration {
				slot_duration: Babe::slot_duration(),
				epoch_length: EpochDuration::get(),
				c: PRIMARY_PROBABILITY,
				genesis_authorities: Babe::authorities(),
				randomness: Babe::randomness(),
				allowed_slots: sp_consensus_babe::AllowedSlots::PrimaryAndSecondaryPlainSlots,
			}
		}

		fn current_epoch_start() -> sp_consensus_babe::Slot {
			Babe::current_epoch_start()
		}

		fn current_epoch() -> sp_consensus_babe::Epoch {
			Babe::current_epoch()
		}

		fn next_epoch() -> sp_consensus_babe::Epoch {
			Babe::next_epoch()
		}

		fn generate_key_ownership_proof(
			_slot: sp_consensus_babe::Slot,
			authority_id: sp_consensus_babe::AuthorityId,
		) -> Option<sp_consensus_babe::OpaqueKeyOwnershipProof> {
			use codec::Encode;

			Historical::prove((sp_consensus_babe::KEY_TYPE, authority_id))
				.map(|p| p.encode())
				.map(sp_consensus_babe::OpaqueKeyOwnershipProof::new)
		}

		fn submit_report_equivocation_unsigned_extrinsic(
			equivocation_proof: sp_consensus_babe::EquivocationProof<<Block as BlockT>::Header>,
			key_owner_proof: sp_consensus_babe::OpaqueKeyOwnershipProof,
		) -> Option<()> {
			let key_owner_proof = key_owner_proof.decode()?;

			Babe::submit_unsigned_equivocation_report(
				equivocation_proof,
				key_owner_proof,
			)
		}
	}

	impl sp_authority_discovery::AuthorityDiscoveryApi<Block> for Runtime {
		fn authorities() -> Vec<AuthorityDiscoveryId> {
			AuthorityDiscovery::authorities()
		}
	}

	impl frame_system_rpc_runtime_api::AccountNonceApi<Block, AccountId, Index> for Runtime {
		fn account_nonce(account: AccountId) -> Index {
			System::account_nonce(account)
		}
	}

	/* impl pallet_contracts_rpc_runtime_api::ContractsApi<Block, AccountId, Balance, BlockNumber>
		for Runtime
	{
		fn call(
			origin: AccountId,
			dest: AccountId,
			value: Balance,
			gas_limit: u64,
			input_data: Vec<u8>,
		) -> pallet_contracts_primitives::ContractExecResult {
			Contracts::bare_call(origin, dest, value, gas_limit, input_data)
		}

		fn get_storage(
			address: AccountId,
			key: [u8; 32],
		) -> pallet_contracts_primitives::GetStorageResult {
			Contracts::get_storage(address, key)
		}

		fn rent_projection(
			address: AccountId,
		) -> pallet_contracts_primitives::RentProjectionResult<BlockNumber> {
			Contracts::rent_projection(address)
		}
	} */

	impl fp_rpc::EthereumRuntimeRPCApi<Block> for Runtime {
		fn chain_id() -> u64 {
			<Runtime as pallet_evm::Config>::ChainId::get()
		}

		fn account_basic(address: H160) -> EVMAccount {
			Evm::account_basic(&address)
		}

		fn gas_price() -> U256 {
			<Runtime as pallet_evm::Config>::FeeCalculator::min_gas_price()
		}

		fn account_code_at(address: H160) -> Vec<u8> {
			Evm::account_codes(address)
		}

		fn author() -> H160 {
			<pallet_evm::Module<Runtime>>::find_author()
		}

		fn storage_at(address: H160, index: U256) -> H256 {
			let mut tmp = [0u8; 32];
			index.to_big_endian(&mut tmp);
			Evm::account_storages(address, H256::from_slice(&tmp[..]))
		}

		fn call(
			from: H160,
			to: H160,
			data: Vec<u8>,
			value: U256,
			gas_limit: U256,
			gas_price: Option<U256>,
			nonce: Option<U256>,
			estimate: bool,
		) -> Result<pallet_evm::CallInfo, sp_runtime::DispatchError> {
			let config = if estimate {
				let mut config = <Runtime as pallet_evm::Config>::config().clone();
				config.estimate = true;
				Some(config)
			} else {
				None
			};

			<Runtime as pallet_evm::Config>::Runner::call(
				from,
				to,
				data,
				value,
				gas_limit.low_u64(),
				gas_price,
				nonce,
				config.as_ref().unwrap_or(<Runtime as pallet_evm::Config>::config()),
			).map_err(|err| err.into())
		}

		fn create(
			from: H160,
			data: Vec<u8>,
			value: U256,
			gas_limit: U256,
			gas_price: Option<U256>,
			nonce: Option<U256>,
			estimate: bool,
		) -> Result<pallet_evm::CreateInfo, sp_runtime::DispatchError> {
			let config = if estimate {
				let mut config = <Runtime as pallet_evm::Config>::config().clone();
				config.estimate = true;
				Some(config)
			} else {
				None
			};

			<Runtime as pallet_evm::Config>::Runner::create(
				from,
				data,
				value,
				gas_limit.low_u64(),
				gas_price,
				nonce,
				config.as_ref().unwrap_or(<Runtime as pallet_evm::Config>::config()),
			).map_err(|err| err.into())
		}

		fn current_transaction_statuses() -> Option<Vec<TransactionStatus>> {
			Ethereum::current_transaction_statuses()
		}

		fn current_block() -> Option<pallet_ethereum::Block> {
			Ethereum::current_block()
		}

		fn current_receipts() -> Option<Vec<pallet_ethereum::Receipt>> {
			Ethereum::current_receipts()
		}

		fn current_all() -> (
			Option<pallet_ethereum::Block>,
			Option<Vec<pallet_ethereum::Receipt>>,
			Option<Vec<TransactionStatus>>
		) {
			(
				Ethereum::current_block(),
				Ethereum::current_receipts(),
				Ethereum::current_transaction_statuses()
			)
		}

		fn extrinsic_filter(
			xts: Vec<<Block as BlockT>::Extrinsic>,
		) -> Vec<EthereumTransaction> {
			xts.into_iter().filter_map(|xt| match xt.function {
				Call::Ethereum(transact(t)) => Some(t),
				_ => None
			}).collect::<Vec<EthereumTransaction>>()
		}
	}

	impl pallet_transaction_payment_rpc_runtime_api::TransactionPaymentApi<
		Block,
		Balance,
	> for Runtime {
		fn query_info(uxt: <Block as BlockT>::Extrinsic, len: u32) -> RuntimeDispatchInfo<Balance> {
			TransactionPayment::query_info(uxt, len)
		}
		fn query_fee_details(uxt: <Block as BlockT>::Extrinsic, len: u32) -> FeeDetails<Balance> {
			TransactionPayment::query_fee_details(uxt, len)
		}
	}

	impl pallet_mmr::primitives::MmrApi<
		Block,
		mmr::Leaf,
		mmr::Hash,
	> for Runtime {
		fn generate_proof(leaf_index: u64) -> Result<(mmr::Leaf, mmr::Proof<mmr::Hash>), mmr::Error> {
			Mmr::generate_proof(leaf_index)
		}

		fn verify_proof(leaf: mmr::Leaf, proof: mmr::Proof<mmr::Hash>) -> Result<(), mmr::Error> {
			Mmr::verify_leaf(leaf, proof)
		}

		fn verify_proof_stateless(
			root: mmr::Hash,
			leaf: Vec<u8>,
			proof: mmr::Proof<mmr::Hash>
		) -> Result<(), mmr::Error> {
			let node = mmr::DataOrHash::Data(mmr::OpaqueLeaf(leaf));
			pallet_mmr::verify_leaf_proof::<mmr::Hashing, _>(root, node, proof)
		}
	}

	impl sp_session::SessionKeys<Block> for Runtime {
		fn generate_session_keys(seed: Option<Vec<u8>>) -> Vec<u8> {
			SessionKeys::generate(seed)
		}

		fn decode_session_keys(
			encoded: Vec<u8>,
		) -> Option<Vec<(Vec<u8>, KeyTypeId)>> {
			SessionKeys::decode_into_raw_public_keys(&encoded)
		}
	}

	#[cfg(feature = "runtime-benchmarks")]
	impl frame_benchmarking::Benchmark<Block> for Runtime {
		fn dispatch_benchmark(
			config: frame_benchmarking::BenchmarkConfig
		) -> Result<Vec<frame_benchmarking::BenchmarkBatch>, sp_runtime::RuntimeString> {
			use frame_benchmarking::{Benchmarking, BenchmarkBatch, add_benchmark, TrackedStorageKey};
			// Trying to add benchmarks directly to the Session Pallet caused cyclic dependency issues.
			// To get around that, we separated the Session benchmarks into its own crate, which is why
			// we need these two lines below.
			use pallet_session_benchmarking::Module as SessionBench;
			use pallet_offences_benchmarking::Module as OffencesBench;
			use frame_system_benchmarking::Module as SystemBench;

			use pallet_evm::Module as PalletEvmBench;

			impl pallet_session_benchmarking::Config for Runtime {}
			impl pallet_offences_benchmarking::Config for Runtime {}
			impl frame_system_benchmarking::Config for Runtime {}

			let whitelist: Vec<TrackedStorageKey> = vec![
				// Block Number
				hex_literal::hex!("26aa394eea5630e07c48ae0c9558cef702a5c1b19ab7a04f536c519aca4983ac").to_vec().into(),
				// Total Issuance
				hex_literal::hex!("c2261276cc9d1f8598ea4b6a74b15c2f57c875e4cff74148e4628f264b974c80").to_vec().into(),
				// Execution Phase
				hex_literal::hex!("26aa394eea5630e07c48ae0c9558cef7ff553b5a9862a516939d82b3d3d8661a").to_vec().into(),
				// Event Count
				hex_literal::hex!("26aa394eea5630e07c48ae0c9558cef70a98fdbe9ce6c55837576c60c7af3850").to_vec().into(),
				// System Events
				hex_literal::hex!("26aa394eea5630e07c48ae0c9558cef780d41e5e16056765bc8461851072c9d7").to_vec().into(),
				// Treasury Account
				hex_literal::hex!("26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da95ecffd7b6c0f78751baa9d281e0bfa3a6d6f646c70792f74727372790000000000000000000000000000000000000000").to_vec().into(),
			];

			let mut batches = Vec::<BenchmarkBatch>::new();
			let params = (&config, &whitelist);

			add_benchmark!(params, batches, pallet_evm, PalletEvmBench::<Runtime>);
			add_benchmark!(params, batches, pallet_assets, Assets);
			add_benchmark!(params, batches, pallet_babe, Babe);
			add_benchmark!(params, batches, pallet_balances, Balances);
			add_benchmark!(params, batches, pallet_bounties, Bounties);
			add_benchmark!(params, batches, pallet_collective, Council);
			// add_benchmark!(params, batches, pallet_contracts, Contracts);
			add_benchmark!(params, batches, pallet_democracy, Democracy);
			// add_benchmark!(params, batches, pallet_elections_phragmen, Elections);
			add_benchmark!(params, batches, pallet_grandpa, Grandpa);
			add_benchmark!(params, batches, pallet_identity, Identity);
			add_benchmark!(params, batches, pallet_im_online, ImOnline);
			add_benchmark!(params, batches, pallet_indices, Indices);
			add_benchmark!(params, batches, pallet_lottery, Lottery);
			add_benchmark!(params, batches, pallet_mmr, Mmr);
			// add_benchmark!(params, batches, pallet_multisig, Multisig);
			add_benchmark!(params, batches, pallet_offences, OffencesBench::<Runtime>);
			// add_benchmark!(params, batches, pallet_proxy, Proxy);
			add_benchmark!(params, batches, pallet_scheduler, Scheduler);
			add_benchmark!(params, batches, pallet_session, SessionBench::<Runtime>);
			add_benchmark!(params, batches, pallet_staking, Staking);
			add_benchmark!(params, batches, frame_system, SystemBench::<Runtime>);
			add_benchmark!(params, batches, pallet_timestamp, Timestamp);
			// add_benchmark!(params, batches, pallet_tips, Tips);
			add_benchmark!(params, batches, pallet_treasury, Treasury);
			add_benchmark!(params, batches, pallet_utility, Utility);
			// add_benchmark!(params, batches, pallet_vesting, Vesting);

			if batches.is_empty() { return Err("Benchmark not found for this pallet.".into()) }
			Ok(batches)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use frame_system::offchain::CreateSignedTransaction;

	#[test]
	fn validate_transaction_submitter_bounds() {
		fn is_submit_signed_transaction<T>() where
			T: CreateSignedTransaction<Call>,
		{}

		is_submit_signed_transaction::<Runtime>();
	}
}
