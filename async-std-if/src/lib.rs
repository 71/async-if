//! Wrapper around the Rust standard library, `async-std` and `tokio` to dynamically choose a
//! desired implementation of common functions at compile-time.
#![no_std]

#[cfg(feature = "std")]
extern crate std;

#[doc(hidden)]
pub use async_if;

mod helpers;
mod time;

pub use time::Time;

/// Marker type used to represent (synchronous) `std`-based function implementations.
#[cfg(feature = "std")]
#[derive(Debug, Clone, Copy)]
pub struct Std;

#[cfg(feature = "std")]
impl Std {
    /// `false`, indicating that standard library functions are not asynchronous.
    pub const IS_ASYNC: bool = false;
}

/// Marker type used to represent (asynchronous) `async-std`-based function implementations.
#[cfg(feature = "async-std")]
#[derive(Debug, Clone, Copy)]
pub struct AsyncStd;

#[cfg(feature = "async-std")]
impl AsyncStd {
    /// `true`, indicating that `async-std` functions are not asynchronous.
    pub const IS_ASYNC: bool = true;
}

/// Marker type used to represent (asynchronous) `tokio`-based function implementations.
#[cfg(feature = "tokio")]
#[derive(Debug, Clone, Copy)]
pub struct Tokio;

#[cfg(feature = "tokio")]
impl Tokio {
    /// `true`, indicating that `tokio` functions are not asynchronous.
    pub const IS_ASYNC: bool = true;
}
