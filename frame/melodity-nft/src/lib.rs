//! # Non Fungible Token
//! The module provides implementations for non-fungible-token.
//!
//! - [`Config`](./trait.Config.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! This module provides basic functions to create and manager
//! NFT(non fungible token) such as `create_class`, `transfer`, `mint`, `burn`.

//! ### Module Functions
//!
//! - `create_class` - Create NFT(non fungible token) class
//! - `transfer` - Transfer NFT(non fungible token) to another account.
//! - `mint` - Mint NFT(non fungible token)
//! - `burn` - Burn NFT(non fungible token)
//! - `destroy_class` - Destroy NFT(non fungible token) class

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::unused_unit)]

use codec::{Decode, Encode};
use frame_support::{ensure, pallet_prelude::*, Parameter};
use sp_runtime::{
	traits::{
		AtLeast32BitUnsigned, CheckedAdd, CheckedSub, MaybeSerializeDeserialize, Member, One, Zero
	},
	DispatchError, DispatchResult, RuntimeDebug
};
use sp_std::vec::Vec;
use frame_system::pallet_prelude::OriginFor;
use frame_system::{ensure_root, ensure_signed};

#[cfg(feature = "std")]
use serde::{
	Serialize,
	Deserialize
};

mod mock;
mod tests;

/// Class info
#[derive(Encode, Decode, Clone, Eq, PartialEq, RuntimeDebug)]
pub struct ClassInfo<TokenId, AccountId, Data> {
	/// Total issuance for the class
	pub total_issuance: TokenId,
	/// Class owner
	pub owner: AccountId,
	/// Class Properties
	pub data: Data,
	/// Class metadata
	pub metadata: Vec<u8>,
}

/// Token info
#[derive(Encode, Decode, Clone, Eq, PartialEq, RuntimeDebug)]
pub struct TokenInfo<AccountId, Data> {
	/// Token owner
	pub owner: AccountId,
	/// Token Properties
	pub data: Data,
}

/// MELT token data
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Encode, Decode, Clone, Eq, PartialEq, RuntimeDebug)]
pub struct MelodityNFTData {
	pub json: Vec<u8>,
}

#[frame_support::pallet]
pub mod module {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
		/// The class ID type
		type ClassId: Parameter + Member + AtLeast32BitUnsigned + Default + Copy;
		/// The token ID type
		type TokenId: Parameter + Member + AtLeast32BitUnsigned + Default + Copy;
		/// The class properties type
		type ClassData: Parameter + Member + MaybeSerializeDeserialize;
		/// The token properties type
		type TokenData: Parameter + Member + MaybeSerializeDeserialize;
	}

	pub type ClassInfoOf<T> =
		ClassInfo<<T as Config>::TokenId, <T as frame_system::Config>::AccountId, <T as Config>::ClassData>;
	pub type TokenInfoOf<T> = TokenInfo<<T as frame_system::Config>::AccountId, <T as Config>::TokenData>;

	pub type GenesisTokenData<T> = (
		<T as frame_system::Config>::AccountId, // Token owner
		<T as Config>::TokenData,
	);
	pub type GenesisTokens<T> = (
		<T as frame_system::Config>::AccountId, // Token class owner
		Vec<u8>,                                // Token class metadata
		<T as Config>::ClassData,
		Vec<GenesisTokenData<T>>, // Vector of tokens belonging to this class
	);

	/// Error for non-fungible-token module.
	#[pallet::error]
	pub enum Error<T> {
		/// No available class ID
		NoAvailableClassId,
		/// No available token ID
		NoAvailableTokenId,
		/// Token(ClassId, TokenId) not found
		TokenNotFound,
		/// Class not found
		ClassNotFound,
		/// The operator is not the owner of the token and has no permission
		NoPermission,
		/// Arithmetic calculation overflow
		NumOverflow,
		/// Can not destroy class
		/// Total issuance is not 0
		CannotDestroyClass,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Nft class creation completed successfully \[class_identifier, class_metadata\]
		ClassCreated(T::ClassId, T::ClassData),
		/// Nft class distruction completed successfully \[class_identifier\]
		ClassDestroyed(T::ClassId),
		/// Nft transfer completed successfully \[class_identifier, token_identifier, sender, receiver\]
		TransferCompleted(T::ClassId, T::TokenId, T::AccountId, T::AccountId),
		/// Nft creation completed \[class_identifier, token_identifier, receiver\]
		Mint(T::ClassId, T::TokenId, T::AccountId),
		/// Nft burn completed \[class_identifier, token_identifier, burner\]
		Burn(T::ClassId, T::TokenId, T::AccountId),
	}

	/// Next available class ID.
	#[pallet::storage]
	#[pallet::getter(fn next_class_id)]
	pub type NextClassId<T: Config> = StorageValue<_, T::ClassId, ValueQuery>;

	/// Next available token ID.
	#[pallet::storage]
	#[pallet::getter(fn next_token_id)]
	pub type NextTokenId<T: Config> = StorageMap<_, Twox64Concat, T::ClassId, T::TokenId, ValueQuery>;

	/// Store class info.
	///
	/// Returns `None` if class info not set or removed.
	#[pallet::storage]
	#[pallet::getter(fn classes)]
	pub type Classes<T: Config> = StorageMap<_, Twox64Concat, T::ClassId, ClassInfoOf<T>>;

	/// Store token info.
	///
	/// Returns `None` if token info not set or removed.
	#[pallet::storage]
	#[pallet::getter(fn tokens)]
	pub type Tokens<T: Config> =
		StorageDoubleMap<_, Twox64Concat, T::ClassId, Twox64Concat, T::TokenId, TokenInfoOf<T>>;

	/// Token existence check by owner and class ID.
	// TODO: pallet macro doesn't support conditional compiling. Always having `TokensByOwner` storage doesn't hurt but
	// it could be removed once conditional compiling supported.
	// #[cfg(not(feature = "disable-tokens-by-owner"))]
	#[pallet::storage]
	#[pallet::getter(fn tokens_by_owner)]
	pub type TokensByOwner<T: Config> =
		StorageDoubleMap<_, Twox64Concat, T::AccountId, Twox64Concat, (T::ClassId, T::TokenId), (), ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub tokens: Vec<GenesisTokens<T>>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			GenesisConfig { tokens: vec![] }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			self.tokens.iter().for_each(|token_class| {
				let class_id = Pallet::<T>::internal_create_class(
					&token_class.0, 
					token_class.1.to_vec(), 
					token_class.2.clone()
				).expect("Create class cannot fail while building genesis");
				for (account_id, token_data) in &token_class.3 {
					Pallet::<T>::internal_mint(
						&account_id, 
						class_id, 
						token_data.clone()
					).expect("Token mint cannot fail during genesis");
				}
			})
		}
	}

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Create NFT(non fungible token) class
		#[pallet::weight(100_000_000)]
		pub fn create_class(
			origin: OriginFor<T>,
			owner: T::AccountId,
			metadata: Vec<u8>,
			data: T::ClassData,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;

			let class_id = NextClassId::<T>::try_mutate(|id| -> Result<T::ClassId, DispatchError> {
				let current_id = *id;
				*id = id.checked_add(&One::one()).ok_or(Error::<T>::NoAvailableClassId)?;
				Ok(current_id)
			})?;

			let info = ClassInfo {
				metadata,
				total_issuance: Default::default(),
				owner: owner.clone(),
				data: data.clone(),
			};
			Classes::<T>::insert(class_id, info);

			// emit class creation event
			Self::deposit_event(Event::ClassCreated(class_id, data));

			Ok(().into())
		}

		/// Transfer NFT(non fungible token) from `from` account to `to` account
		#[pallet::weight(100_000_000)]
		pub fn transfer(
			origin: OriginFor<T>,
			to: T::AccountId, 
			token: (T::ClassId, T::TokenId)
		) -> DispatchResultWithPostInfo {
			// ensure the transaction is signed
			let from = ensure_signed(origin)?;
			Tokens::<T>::try_mutate(token.0, token.1, |token_info| -> DispatchResultWithPostInfo {
				let mut info = token_info.as_mut().ok_or(Error::<T>::TokenNotFound)?;
				
				// ensure the owner of the nft is the transaction sender
				ensure!(info.owner == from, Error::<T>::NoPermission);

				if from == to {
					// no change needed
					return Ok(().into());
				}

				info.owner = to.clone();

				#[cfg(not(feature = "disable-tokens-by-owner"))]
				{
					TokensByOwner::<T>::remove(from.clone(), token);
					TokensByOwner::<T>::insert(to.clone(), token, ());
				}

				Self::deposit_event(Event::TransferCompleted(token.0, token.1, from, to));

				Ok(().into())
			})
		}

		/// Mint NFT(non fungible token) to `owner`
		#[pallet::weight(100_000_000)]
		pub fn mint(
			origin: OriginFor<T>,
			owner: T::AccountId,
			class_id: T::ClassId,
			data: T::TokenData,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			NextTokenId::<T>::try_mutate(class_id, |id| -> DispatchResultWithPostInfo {
				let token_id = *id;
				*id = id.checked_add(&One::one()).ok_or(Error::<T>::NoAvailableTokenId)?;

				Classes::<T>::try_mutate(class_id, |class_info| -> DispatchResult {
					let info = class_info.as_mut().ok_or(Error::<T>::ClassNotFound)?;
					info.total_issuance = info
						.total_issuance
						.checked_add(&One::one())
						.ok_or(Error::<T>::NumOverflow)?;
					Ok(())
				})?;

				let token_info = TokenInfo {
					owner: owner.clone(),
					data,
				};
				Tokens::<T>::insert(class_id, token_id, token_info);

				#[cfg(not(feature = "disable-tokens-by-owner"))]
				TokensByOwner::<T>::insert(owner.clone(), (class_id, token_id), ());

				Self::deposit_event(Event::Mint(class_id, token_id, owner));

				Ok(().into())
			})
		}

		/// Burn NFT(non fungible token) from `owner`
		#[pallet::weight(100_000_000)]
		pub fn burn(
			origin: OriginFor<T>,
			token: (T::ClassId, T::TokenId)
		) -> DispatchResultWithPostInfo {
			// ensure the message is signed
			let from = ensure_signed(origin)?;
			Tokens::<T>::try_mutate_exists(token.0, token.1, |token_info| -> DispatchResultWithPostInfo {
				let t = token_info.take().ok_or(Error::<T>::TokenNotFound)?;

				// ansure the actuall caller of this method is the owner of the nft
				ensure!(t.owner == from, Error::<T>::NoPermission);

				// reduce the total issuance amount
				Classes::<T>::try_mutate(token.0, |class_info| -> DispatchResult {
					let info = class_info.as_mut().ok_or(Error::<T>::ClassNotFound)?;
					info.total_issuance = info
						.total_issuance
						.checked_sub(&One::one())
						.ok_or(Error::<T>::NumOverflow)?;
					Ok(())
				})?;

				#[cfg(not(feature = "disable-tokens-by-owner"))]
				TokensByOwner::<T>::remove(from.clone(), token);

				Self::deposit_event(Event::Burn(token.0, token.1, from));

				Ok(().into())
			})
		}

		/// Forcefully burn NFT from 'owner'
		#[pallet::weight(100_000_000)]
		pub fn force_burn(
			origin: OriginFor<T>,
			owner: T::AccountId,
			token: (T::ClassId, T::TokenId)
		) -> DispatchResultWithPostInfo {
			// ensure the message comes from root
			ensure_root(origin)?;
			Tokens::<T>::try_mutate_exists(token.0, token.1, |token_info| -> DispatchResultWithPostInfo {
				token_info.take().ok_or(Error::<T>::TokenNotFound)?;

				// reduce the total issuance amount
				Classes::<T>::try_mutate(token.0, |class_info| -> DispatchResult {
					let info = class_info.as_mut().ok_or(Error::<T>::ClassNotFound)?;
					info.total_issuance = info
						.total_issuance
						.checked_sub(&One::one())
						.ok_or(Error::<T>::NumOverflow)?;
					Ok(())
				})?;

				#[cfg(not(feature = "disable-tokens-by-owner"))]
				TokensByOwner::<T>::remove(owner.clone(), token);

				Self::deposit_event(Event::Burn(token.0, token.1, owner));

				Ok(().into())
			})
		}

		/// Destroy NFT(non fungible token) class
		#[pallet::weight(100_000_000)]
		pub fn destroy_class(
			origin: OriginFor<T>,
			class_id: T::ClassId
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			Classes::<T>::try_mutate_exists(class_id, |class_info| -> DispatchResultWithPostInfo {
				let info = class_info.take().ok_or(Error::<T>::ClassNotFound)?;
				ensure!(info.total_issuance == Zero::zero(), Error::<T>::CannotDestroyClass);

				NextTokenId::<T>::remove(class_id);

				Self::deposit_event(Event::ClassDestroyed(class_id));

				Ok(().into())
			})
		}
	}
}

pub use module::*;

impl<T: Config> Pallet<T> {
	/// Create NFT(non fungible token) class
	pub fn internal_create_class(
		owner: &T::AccountId,
		metadata: Vec<u8>,
		data: T::ClassData,
	) -> Result<T::ClassId, DispatchError> {
		let class_id = NextClassId::<T>::try_mutate(|id| -> Result<T::ClassId, DispatchError> {
			let current_id = *id;
			*id = id.checked_add(&One::one()).ok_or(Error::<T>::NoAvailableClassId)?;
			Ok(current_id)
		})?;

		let info = ClassInfo {
			metadata,
			total_issuance: Default::default(),
			owner: owner.clone(),
			data,
		};
		Classes::<T>::insert(class_id, info);

		Ok(class_id)
	}

	pub fn internal_mint(
		owner: &T::AccountId,
		class_id: T::ClassId,
		data: T::TokenData,
	) -> Result<T::TokenId, DispatchError>  {
		NextTokenId::<T>::try_mutate(class_id, |id| -> Result<T::TokenId, DispatchError> {
			let token_id = *id;
			*id = id.checked_add(&One::one()).ok_or(Error::<T>::NoAvailableTokenId)?;

			Classes::<T>::try_mutate(class_id, |class_info| -> DispatchResult {
				let info = class_info.as_mut().ok_or(Error::<T>::ClassNotFound)?;
				info.total_issuance = info
					.total_issuance
					.checked_add(&One::one())
					.ok_or(Error::<T>::NumOverflow)?;
				Ok(())
			})?;

			let token_info = TokenInfo {
				owner: owner.clone(),
				data,
			};
			Tokens::<T>::insert(class_id, token_id, token_info);
			#[cfg(not(feature = "disable-tokens-by-owner"))]
			TokensByOwner::<T>::insert(owner, (class_id, token_id), ());

			Ok(token_id)
		})
	}

	pub fn is_owner(
		account: &T::AccountId, 
		token: (T::ClassId, T::TokenId)
	) -> bool {
		#[cfg(feature = "disable-tokens-by-owner")]
		return Tokens::<T>::get(token.0, token.1).map_or(false, |token| token.owner == *account);

		#[cfg(not(feature = "disable-tokens-by-owner"))]
		TokensByOwner::<T>::contains_key(account, token)
	}
}

pub trait NftExistance<T, U, V> {
	fn exists(class_id: T, nft_id: U) -> bool;
	fn owns(account: V, class_id: T, nft_id: U) -> bool;
}

impl<T: Config> NftExistance<T::ClassId, T::TokenId, T::AccountId> for Pallet<T> {
	fn exists(class_id: T::ClassId, nft_id: T::TokenId) -> bool {
		Tokens::<T>::contains_key(class_id, nft_id)
	}

	fn owns(account: T::AccountId, class_id: T::ClassId, nft_id: T::TokenId) -> bool {
		TokensByOwner::<T>::contains_key(account, (class_id, nft_id))
	}
}