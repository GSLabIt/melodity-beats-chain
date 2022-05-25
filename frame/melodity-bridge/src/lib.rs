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
//! - `set_available_meld` - Set the available amount of MELD in the bridge 
//! 						wallet
//! - `convert` - Takes the defined amount of MELB and burns them, the
//! 				bridge listener will be responsible for the sending
//! 				of tokens
//! - `set_conversion_fee` - Set the conversion fee taken by the platform
//! - `set_minimum_conversion_amount` - Set the minimum amount required to be converted
//! - `check_change_rate` - Return the current change rate

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::unused_unit)]

use sp_std::convert::TryInto;
use frame_support::{
	ensure, pallet_prelude::*, // Parameter, // unused
	traits::{
		Currency, ReservableCurrency, WithdrawReasons, ExistenceRequirement
	},
};
use sp_runtime::{
	traits::{
		One, // CheckedSub, Zero,  // unused
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
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

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
		type FeeDecimalPositions: Get<u128>;
	}

	/// Error for non-fungible-token module.
	#[pallet::error]
	pub enum Error<T> {
		/// Conversion amount is less than required minimum conversion 
		ConversionAmountTooLow,
		/// Conversion amount is too high for being converted in one 
		/// transaction only, split it in 2 or more transactions
		ConversionAmountTooHigh,
		/// Provided wallet address is not valid 
		InvalidWalletAddress,
		/// Not enough liquidity to perform the conversion
		NotEnoughLiquidity,
		/// Bridge error, liquidity exhausted
		BridgeExhausted,
		/// Numeric overflow in conversion
		Overflow,
		/// Conversion between incompatible types
		IncompatibleTypes
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// MELB converted successfully \[BSC_address, MELD_amount\]
		Converted(Vec<u8>, u128),
		/// Fee taken successfully \[token_owner, taken_fee, converted_amount\]
		FeeTaken(T::AccountId, u128, u128),
		/// Available MELD for bridge conversion updated sucessfully \[available_meld\]
		AvailableMELDUpdated(u128),
		/// Platform fee for bridge conversion updated sucessfully \[fee\]
		FeeUpdated(u128),
		/// Minimum conversion amount updated sucessfully \[minimum_conversion_amount\]
		MinimumConversionAmountUpdated(u128),
	}

	/// Available MELD in the bridge wallet.
	/// The value is saved with 18 decimals
	#[pallet::storage]
	#[pallet::getter(fn available_meld)]
	pub type AvailableMeld<T> = StorageValue<_, u128, ValueQuery>;

	/// The platform conversion fee, FeeDecimalPositions decimals required	
	#[pallet::storage]
	#[pallet::getter(fn conversion_fee)]
	pub type ConversionFee<T> = StorageValue<_, u128, ValueQuery>;

	/// Minimum amount to convert before actually doing the conversion
	#[pallet::storage]
	#[pallet::getter(fn minimum_conversion)]
	pub type MinimumConversion<T> = StorageValue<_, u128, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn last_conversion_rate)]
	pub type LastConversionRate<T> = StorageValue<_, (u128, Vec<u8>), ValueQuery>;
	
	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {
		fn on_initialize(n: T::BlockNumber) -> Weight {
			LastConversionRate::<T>::put(Pallet::<T>::compute_change_rate().unwrap());
			0
		}
	}

	#[pallet::genesis_config]
	pub struct GenesisConfig {
		pub bridge_balance: u128,
		pub platform_fee: u128,
		pub conversion_minimum: u128,
	}

	#[cfg(feature = "std")]
	impl Default for GenesisConfig {
		fn default() -> Self {
			GenesisConfig { 
				bridge_balance: 0u128,
				platform_fee: 0u128,
				conversion_minimum: 0u128
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			AvailableMeld::<T>::put(self.bridge_balance);
			ConversionFee::<T>::put(self.platform_fee);
			MinimumConversion::<T>::put(self.conversion_minimum);
		}
	}

	use frame_support::log::{info}; // {info, trace, warn};  // unused

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Create NFT(non fungible token) class
		#[pallet::weight(1_000_000_000)]
		pub fn set_available_meld(
			origin: OriginFor<T>,
			amount: u128,
		) -> DispatchResultWithPostInfo {
			T::ControllerOrigin::ensure_origin(origin)?; 

			// add necessary decimals to amount (18)
			let amount:u128 = amount.checked_mul(10u128.checked_pow(18).ok_or(Error::<T>::Overflow)?).ok_or(Error::<T>::Overflow)?;

			AvailableMeld::<T>::try_mutate(|available_m| -> Result<u128, DispatchError> {
				*available_m = amount;
				Ok(*available_m)
			})?;

			// emit event
			Self::deposit_event(Event::AvailableMELDUpdated(amount));

			Ok(().into())
		}

		/// NOTE: inserted address has to OMIT the '0x' to avoid bad Vec<u8> formatting.
		#[pallet::weight(1_000_000_000)]
		pub fn convert(
			origin: OriginFor<T>,
			bsc_wallet: Vec<u8>, 
			amount: u128
		) -> DispatchResultWithPostInfo {
			// ensure the transaction is signed
			let from = ensure_signed(origin)?;

			// translate amount to have same decimals as MinimumConversion (12 decimals)
			let amount:u128 = amount.checked_mul(10u128.checked_pow(12).ok_or(Error::<T>::Overflow)?).ok_or(Error::<T>::Overflow)?;
			
			info!("AMOUNT TO CONVERT: {}, MINIMUMCONVERSION: {}", amount, MinimumConversion::<T>::get());
			// ensure!(amount >= MinimumConversion::<T>::get(), Error::<T>::ConversionAmountTooLow);
			ensure!(amount >= MinimumConversion::<T>::get(), Error::<T>::ConversionAmountTooLow);


			// avoid overflowing u128 by setting the maximum conversion amount to 1 mln MELB
			// also the amount of MELD in the bridge wallet MUST not exceed 300 mln units
			ensure!(amount <= 1_000_000__000000000000u128, Error::<T>::ConversionAmountTooHigh);

			// wallet regex
			// let re = Regex::new(r"^0x[a-fA-F0-9]{40}$").unwrap(); unusable with no-std env	
			ensure!(bsc_wallet.len() == 40, Error::<T>::InvalidWalletAddress);
			// ensure!(bsc_wallet[0] == '0' as u8 && bsc_wallet[1] == 'x' as u8, Error::<T>::InvalidWalletAddress);
			for i in 0..40 {
				if (bsc_wallet[i] >= 48 && bsc_wallet[i] <= 57) || 
					(bsc_wallet[i] >= 65 && bsc_wallet[i] <= 70) ||
					(bsc_wallet[i] >= 97 && bsc_wallet[i] <= 102) {
					continue;
				}
				else {
					return Err(Error::<T>::InvalidWalletAddress.into());
				}
			}
			info!("ADDRESS OK..");
			
			// compute the fee and the really converted amount
			// conversion fee is in 8 decimals (considering it is a percentage then it is in 10)
			// therefore multiplying by 100 brings it to 12 decimals, which is what is needed
			let mut fee: u128 = amount.checked_mul(ConversionFee::<T>::get().checked_mul(100).ok_or(Error::<T>::Overflow)?).ok_or(Error::<T>::Overflow)?;
			// remove double decimals: prev multiplication gives 24 decimals of precision
			fee = fee.checked_div(10u128.checked_pow(12).ok_or(Error::<T>::Overflow)?).ok_or(Error::<T>::Overflow)?;
			info!("FEE TO PAY FOR AMOUNT: {} is {}", amount, fee);
			// fee = fee.checked_div(T::FeeDecimalPositions::get().checked_mul(100).ok_or(Error::<T>::Overflow)?).ok_or(Error::<T>::Overflow)?;
			info!("FEE COMPUTATION OK..");

			// if the conversion is made by the platform pot itself the fee (that goes to the)
			// same address should not be payed as it is nonsense
			if from == T::PlatformPot::get() {
				fee = 0u128;
			}

			let real_amount: u128 = amount.checked_sub(fee).ok_or(Error::<T>::Overflow)?;
			info!("REAL AMOUNT COMPUTATION OK..");

			info!("REAL AMOUNT: {}, AMOUNT: {}, FEE: {}", real_amount, amount, fee);

			// check the user actually has the funds to perform the conversion
			if T::Currency::free_balance(&from) >= amount.into() {
				// burn the real_amount of token that get converted
				T::Currency::withdraw(&from, real_amount.into(), WithdrawReasons::TRANSACTION_PAYMENT, ExistenceRequirement::AllowDeath)?;
				// transfer to the platform pot the taken fees
				if fee > 0u128 {
					T::Currency::transfer(&from, &T::PlatformPot::get(), fee.into(), ExistenceRequirement::AllowDeath)?;
					// emit event
					Self::deposit_event(Event::FeeTaken(from, fee, real_amount));
				}

				// The conversion rate must be computed inline because the order in which operations gets
				// executed is really important in order to avoid rounding bugs
				// Computation must be executed in the following order:
				// 		real_amount * available_meld / supply 
				// This matters because we are always talking about unsigned integers
				// The computed amount must not be padded with any zeros

				// NOTE: using u128, the following command overflows if all 18 decimals from MELD are used for
				// 	the computation (jump at least to 144bits) in order to avoid this only 12 decimals will be used
				//  this will lead to a disalignment of the decimals after the computation is completed, a re-aligment
				//	is done by multipling the ending value to 1e6.
				// NOTE: using the previous method the last 6 decimal digits will always be 0

				let truncated_available_meld = AvailableMeld::<T>::get().checked_div(1_000_000).ok_or(Error::<T>::Overflow)?;

				// First phase, converted_amount * available_meld
				let mut meld: u128 = real_amount.checked_mul(truncated_available_meld).ok_or(Error::<T>::Overflow)?;

				let issuance: u128 = TryInto::<u128>::try_into(T::Currency::total_issuance())
					.ok()
					.unwrap_or(0);
				if issuance == 0 {
					return Err(Error::<T>::IncompatibleTypes.into());
				}
				// second phase, first_phase / MELB issuance
				meld = meld.checked_div(issuance).ok_or(Error::<T>::Overflow)?;
				// third phase (re-alignment), second_phase * 1e6
				meld = meld.checked_mul(1_000_000).ok_or(Error::<T>::Overflow)?;

				
				AvailableMeld::<T>::try_mutate(|available_m| -> Result<u128, DispatchError> {
					*available_m = available_m.checked_sub(meld).ok_or(Error::<T>::BridgeExhausted)?;
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
		pub fn set_conversion_fee(
			origin: OriginFor<T>,
			fee: u128,
		) -> DispatchResultWithPostInfo {
			T::ControllerOrigin::ensure_origin(origin)?;

			ConversionFee::<T>::put(fee);

			// emit event
			Self::deposit_event(Event::FeeUpdated(fee));

			Ok(().into())
		}

		/// Mint NFT(non fungible token) to `owner`
		#[pallet::weight(1_000_000_000)]
		pub fn set_minimum_conversion_amount(
			origin: OriginFor<T>,
			amount: u128,
		) -> DispatchResultWithPostInfo {
			T::ControllerOrigin::ensure_origin(origin)?;

			MinimumConversion::<T>::put(amount);

			// emit event
			Self::deposit_event(Event::MinimumConversionAmountUpdated(amount));

			Ok(().into())
		}
	}
}

pub use pallet::*;
use frame_support::log::{info}; // {info, trace, warn};  // unused

impl<T: Config> Pallet<T> {
	/// compute the current change rate
	pub fn compute_change_rate() -> Result<(u128, Vec<u8>), DispatchError> {
		let mut rate: u128 = 0;
		let mut unit: Vec<u8> = "MELB".as_bytes().to_vec();
		if AvailableMeld::<T>::get() > 0 {
			let mut issuance = TryInto::<u128>::try_into(T::Currency::total_issuance())
				.ok()
				.unwrap_or(1);

			if issuance == 0 {
				return Err(Error::<T>::IncompatibleTypes.into());
			}
			if issuance == u128::MAX {
				issuance = 1;
			}
			let truncated_available_meld = AvailableMeld::<T>::get().checked_div(1_000_000).ok_or(Error::<T>::Overflow)?;
			rate = truncated_available_meld.checked_div(issuance).ok_or(Error::<T>::Overflow)?;
			
			// static values
			const A: u128 = 1_000;
			const B: u128 = 1_000_000;
			const C: u128 = 1_000_000_000;
			const D: u128 = 1_000_000_000_000;
			const E: u128 = 1_000_000_000_000_000;
			const F: u128 = 1_000_000_000_000_000_000;
			const G: u128 = 1_000_000_000_000_000_000_000;
			const H: u128 = 1_000_000_000_000_000_000_000_000;
			const I: u128 = 1_000_000_000_000_000_000_000_000_000;
			const J: u128 = 1_000_000_000_000_000_000_000_000_000_000;
			const K: u128 = 1_000_000_000_000_000_000_000_000_000_000_000;


			let mut multiplier: u128 = One::one();

			// if the rate is zero the change rate is lower than the precision
			while rate == 0 {
				multiplier = multiplier.checked_mul(1_000).ok_or(Error::<T>::Overflow)?;
				match multiplier {
					A => unit = "thousand MELB".as_bytes().to_vec(),
					B => unit = "million MELB".as_bytes().to_vec(),
					C => unit = "billion MELB".as_bytes().to_vec(),
					D => unit = "trillion MELB".as_bytes().to_vec(),
					E => unit = "quadrillion MELB".as_bytes().to_vec(),
					F => unit = "quintillion MELB".as_bytes().to_vec(),
					G => unit = "sextillion MELB".as_bytes().to_vec(),
					H => unit = "septillion MELB".as_bytes().to_vec(),
					I => unit = "octillion MELB".as_bytes().to_vec(),
					J => unit = "nonillion MELB".as_bytes().to_vec(),
					K => unit = "decillion MELB".as_bytes().to_vec(),
					_ => unit = "undicillion MELB".as_bytes().to_vec(),
				}
				rate = multiplier.checked_mul(truncated_available_meld).ok_or(Error::<T>::Overflow)?;

				issuance = TryInto::<u128>::try_into(T::Currency::total_issuance())
					.ok()
					.unwrap_or(0);
				if issuance == 0 {
					return Err(Error::<T>::IncompatibleTypes.into());
				}

				rate = rate.checked_div(issuance).ok_or(Error::<T>::Overflow)?;
			}
		}

		rate = rate.checked_mul(1_000_000).ok_or(Error::<T>::Overflow)?;
		/*
		// decomment to actively notice the change rate
		info!("RATE: {}, UNIT:", rate);
		for i in &unit{
			info!("{}", *i as char);
		}
		*/
		Ok((rate, unit))
	}
}