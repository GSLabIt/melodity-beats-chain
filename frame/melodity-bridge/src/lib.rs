//! # Bridge module
//! The module provides implementations for the bridge functionalities.
//!
//! - [`Config`](./trait.Config.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! This module provides basic functions to keep track of the available
//! MELD and to reduce the supply on a migration.

//! ### Module Functions
//!
//! - `setAvailableMELD` - Set the available amount of MELD in the bridge 
//! 						wallet
//! - `convert` - Takes the defined amount of MELB and burns them, the
//! 				bridge listener will be responsible for the sending
//! 				of tokens
//! - `setConversionFee` - Set the conversion fee taken by the platform
//! - `setMinimumConversionAmount` - Set the minimum amount required to be converted
//! - `checkChangeRate` - Return the current change rate

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::unused_unit)]

use frame_support::{
	ensure, pallet_prelude::*, Parameter,
	traits::{
		Currency, ReservableCurrency, WithdrawReasons, ExistenceRequirement
	},
	debug::native::{
		debug
	}
};
use sp_runtime::{
	traits::{
		CheckedSub, Zero, One,
	},
	DispatchError,  
};
use sp_std::vec::Vec;
use frame_system::pallet_prelude::OriginFor;
use frame_system::{ensure_signed};

mod mock;
mod tests;

type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type Balance = u128;

#[frame_support::pallet]
pub mod module {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Required origin for making all the administrative modifications
		type ControllerOrigin: EnsureOrigin<Self::Origin>;

		/// The currency used for fee payment.
		type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

		/// The address where the conversion fee will be deposited
		type PlatformPot: Get<Self::AccountId>;

		/// The number of decimal positions for the fee definition
		type FeeDecimalPositions: Get<BalanceOf<Self>>;

		/// 100 in the balanceof unit
		type OneHunderd: Get<BalanceOf<Self>>;
	}

	/// Error for non-fungible-token module.
	#[pallet::error]
	pub enum Error<T> {
		/// Conversion amount is less than required minimum conversion 
		ConversionAmountTooLow,
		/// Provided wallet address is not valid 
		InvalidWalletAddress,
		/// Not enough liquidity to perform the conversion
		NotEnoughLiquidity,
		/// Bridge error, liquidity exhausted
		BridgeExhausted,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// MELB converted successfully \[BSC_address, MELD_amount\]
		Converted(Vec<u8>, BalanceOf<T>),
		/// Fee taken successfully \[token_owner, taken_fee, converted_amount, MELD_amount\]
		FeeTaken(T::AccountId, BalanceOf<T>, BalanceOf<T>, BalanceOf<T>),
		/// Available MELD for bridge conversion updated sucessfully \[available_meld\]
		AvailableMELDUpdated(BalanceOf<T>),
		/// Platform fee for bridge conversion updated sucessfully \[fee\]
		FeeUpdated(BalanceOf<T>),
		/// Minimum conversion amount updated sucessfully \[minimum_conversion_amount\]
		MinimumConversionAmountUpdated(BalanceOf<T>),
	}

	/// Available MELD in the bridge wallet.
	/// The value is saved with 18 decimals
	#[pallet::storage]
	#[pallet::getter(fn available_meld)]
	pub type AvailableMeld<T> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// The platform conversion fee, FeeDecimalPositions decimals required	
	#[pallet::storage]
	#[pallet::getter(fn conversion_fee)]
	pub type ConversionFee<T> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// Minimum amount to convert before actually doing the conversion
	#[pallet::storage]
	#[pallet::getter(fn minimum_conversion)]
	pub type MinimumConversion<T> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn last_conversion_rate)]
	pub type LastConversionRate<T> = StorageValue<_, (BalanceOf<T>, Vec<u8>), ValueQuery>;

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {
		fn on_initialize(n: T::BlockNumber) -> Weight {
			LastConversionRate::<T>::put(Pallet::<T>::compute_change_rate().unwrap());
			0
		}
	}

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub bridge_balance: BalanceOf<T>,
		pub platform_fee: BalanceOf<T>,
		pub conversion_minimum: BalanceOf<T>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			GenesisConfig { 
				bridge_balance: Zero::zero(),
				platform_fee: Zero::zero(),
				conversion_minimum: Zero::zero()
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			AvailableMeld::<T>::put(self.bridge_balance);
			ConversionFee::<T>::put(self.platform_fee);
			MinimumConversion::<T>::put(self.conversion_minimum);
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Create NFT(non fungible token) class
		#[pallet::weight(1_000_000_000)]
		pub fn setAvailableMeld(
			origin: OriginFor<T>,
			amount: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			T::ControllerOrigin::ensure_origin(origin)?;

			AvailableMeld::<T>::try_mutate(|available_m| -> Result<BalanceOf<T>, DispatchError> {
				*available_m = amount;
				Ok(*available_m)
			})?;

			// emit event
			Self::deposit_event(Event::AvailableMELDUpdated(amount));

			Ok(().into())
		}

		/// Transfer NFT(non fungible token) from `from` account to `to` account
		#[pallet::weight(1_000_000_000)]
		pub fn convert(
			origin: OriginFor<T>,
			bsc_wallet: Vec<u8>, 
			amount: BalanceOf<T>
		) -> DispatchResultWithPostInfo {
			// ensure the transaction is signed
			let from = ensure_signed(origin)?;
			
			ensure!(amount >= MinimumConversion::<T>::get(), Error::<T>::ConversionAmountTooLow);

			// wallet regex
			// let re = Regex::new(r"^0x[a-fA-F0-9]{40}$").unwrap(); unusable with nostd env
  			frame_support::debug::native::debug!("{:?}", bsc_wallet);

			ensure!(bsc_wallet.len() == 42, Error::<T>::InvalidWalletAddress);
			ensure!(bsc_wallet[0] == '0' as u8 && bsc_wallet[1] == 'x' as u8, Error::<T>::InvalidWalletAddress);
			for i in 2..42 {
				if (bsc_wallet[i] >= 48 && bsc_wallet[i] <= 57) || 
					(bsc_wallet[i] >= 65 && bsc_wallet[i] <= 70) ||
					(bsc_wallet[i] >= 97 && bsc_wallet[i] <= 102) {
					continue;
				}
				else {
					return Err(Error::<T>::InvalidWalletAddress.into());
				}
			}
			
			// compute the fee and the really converted amount
			let mut fee = amount * (ConversionFee::<T>::get() / T::FeeDecimalPositions::get()) / T::OneHunderd::get();
			
			// if the conversion is made by the platform pot itself the fee (that goes to the)
			// same address should not be payed as it is nonsense
			if(from == T::PlatformPot::get()) {
				fee = Zero::zero();
			}

			let real_amount = amount - fee;

			// check the user actually has the funds to perform the conversion
			if(T::Currency::free_balance(&from) >= amount) {
				// burn the real_amount of token that get converted
				T::Currency::withdraw(&from, real_amount, WithdrawReasons::TRANSACTION_PAYMENT, ExistenceRequirement::AllowDeath)?;
				// transfer to the platform pot the taken fees
				if(fee > Zero::zero()) {
					T::Currency::transfer(&from, &T::PlatformPot::get(), fee, ExistenceRequirement::AllowDeath)?;
				}

				// The conversion rate must be computed inline because the order in which operations gets
				// executed is really important in order to avoid rounding bugs
				// Computation must be executed in the following order:
				// 		real_amount * available_meld / supply 
				// This matters because we are always talking about unsigned integers
				// The computed amount must not be padded with any zeros
				let meld = real_amount * AvailableMeld::<T>::get() / T::Currency::total_issuance();
				AvailableMeld::<T>::try_mutate(|available_m| -> Result<BalanceOf<T>, DispatchError> {
					*available_m = amount.checked_sub(&meld).ok_or(Error::<T>::BridgeExhausted)?;
					Ok(*available_m)
				})?;

				// emit event
				Self::deposit_event(Event::Converted(bsc_wallet, meld));

				Ok(().into())
			}
			else {
				Err(Error::<T>::NotEnoughLiquidity.into())
			}
		}

		/// Mint NFT(non fungible token) to `owner`
		#[pallet::weight(1_000_000_000)]
		pub fn setConversionFee(
			origin: OriginFor<T>,
			fee: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			T::ControllerOrigin::ensure_origin(origin)?;

			ConversionFee::<T>::put(fee);

			// emit event
			Self::deposit_event(Event::FeeUpdated(fee));

			Ok(().into())
		}

		/// Mint NFT(non fungible token) to `owner`
		#[pallet::weight(1_000_000_000)]
		pub fn setMinimumConversionAmount(
			origin: OriginFor<T>,
			amount: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			T::ControllerOrigin::ensure_origin(origin)?;

			MinimumConversion::<T>::put(amount);

			// emit event
			Self::deposit_event(Event::MinimumConversionAmountUpdated(amount));

			Ok(().into())
		}
	}
}

pub use module::*;

impl<T: Config> Pallet<T> {
	/// compute the current change rate
	pub fn compute_change_rate() -> Result<(BalanceOf<T>, Vec<u8>), DispatchError> {
		let mut rate = Zero::zero();
		let mut unit: Vec<u8> = "MELB".as_bytes().to_vec();
		if AvailableMeld::<T>::get() > Zero::zero() {
			rate = AvailableMeld::<T>::get() / T::Currency::total_issuance();
			
			// static values
			let a: BalanceOf<T> = (1_000 as u128).into();
			let b: BalanceOf<T> = (1_000_000 as u128).into();
			let c: BalanceOf<T> = (1_000_000_000 as u128).into();
			let d: BalanceOf<T> = (1_000_000_000_000 as u128).into();
			let e: BalanceOf<T> = (1_000_000_000_000_000 as u128).into();
			let f: BalanceOf<T> = (1_000_000_000_000_000_000 as u128).into();
			let g: BalanceOf<T> = (1_000_000_000_000_000_000_000 as u128).into();
			let h: BalanceOf<T> = (1_000_000_000_000_000_000_000_000 as u128).into();
			let i: BalanceOf<T> = (1_000_000_000_000_000_000_000_000_000 as u128).into();
			let j: BalanceOf<T> = (1_000_000_000_000_000_000_000_000_000_000 as u128).into();
			let k: BalanceOf<T> = (1_000_000_000_000_000_000_000_000_000_000_000 as u128).into();


			let mut multiplier: BalanceOf<T> = One::one();
			let mut zeros: u128 = 0;

			// if the rate is zero the change rate is lower than the precision
			while rate == Zero::zero() {
				multiplier *= (1_000 as u128).into();
				zeros += 3;
				match multiplier {
					a => unit = "thousand MELB".as_bytes().to_vec(),
					b => unit = "million MELB".as_bytes().to_vec(),
					c => unit = "billion MELB".as_bytes().to_vec(),
					d => unit = "trillion MELB".as_bytes().to_vec(),
					e => unit = "quadrillion MELB".as_bytes().to_vec(),
					f => unit = "quintillion MELB".as_bytes().to_vec(),
					g => unit = "sextillion MELB".as_bytes().to_vec(),
					h => unit = "septillion MELB".as_bytes().to_vec(),
					i => unit = "octillion MELB".as_bytes().to_vec(),
					j => unit = "nonillion MELB".as_bytes().to_vec(),
					k => unit = "decillion MELB".as_bytes().to_vec(),
					_ => unit = "undicillion MELB".as_bytes().to_vec(),
				}
				rate = multiplier * AvailableMeld::<T>::get() / T::Currency::total_issuance();
			}
		}
		
		Ok((rate, unit))
	}
}