# async-if

An experimental Rust library for generic async functions.

## Warning

This library is a proof-of-concept I made out of curiosity. Its items are
documented and it has some amount of tests, but the following points need
additional work:

1. Safety: the crate uses `unsafe` in several positions. Most notably, pin
   projections used internally may be incorrect.

2. Trait bounds: none of the traits and types (un)implements `Sync` and `Send`.
   This may be unnecessarily restrictive or, in the worst case, unsafe.

3. Testing: more testing is needed, notably to figure out if inference of `A` in
   `AsyncIf<A>` in macro-generated code is correct (and not too restrictive).

## Examples

Demonstrating the `#[async_if]` attribute:

```rust
pub struct Std;
pub struct Tokio;

#[async_if(Self::A)]
pub trait Sleep {
    type A: IsAsync;

    async fn sleep(duration: Duration);
}

#[async_if(Self::A)]
impl Sleep for Std {
    type A = Synchronous;

    async fn sleep(duration: Duration) { std::thread::sleep(duration) }
}

#[async_if(Self::A)]
impl Sleep for Tokio {
    type A = Asynchronous;

    async fn sleep(duration: Duration) { from_future(tokio::time::sleep(duration)).await }
}

async_if::assert_sync(&Std::sleep(Duration::from_millis(100)));
async_if::assert_async(&Tokio::sleep(Duration::from_millis(100)));
```

Support for recursion with no allocations for `Synchronous` futures:

```rust
#[async_if(A, alloc_with = bump)]
async fn factorial<A: IsAsync>(bump: &bumpalo::Bump, n: u8) -> u64 {
    if n == 0 { 1 } else { n as u64 * factorial::<A>(bump, n - 1).await }
}

let bump = bumpalo::Bump::new();  // Bumpalo support requires the `bumpalo` feature.
assert_eq!(factorial::<Synchronous>(&bump, 5).get(), 120);
assert_eq!(bump.allocated_bytes(), 0);

assert_eq!(factorial::<Asynchronous>(&bump, 5).await, 120);
assert_ne!(bump.allocated_bytes(), 0);
```

The `choose()` helper to mix synchronous and asynchronous APIs:

```rust
#[async_if(A)]
async fn sleep<A: IsAsync>(duration: std::time::Duration) {
    choose::<A, _>(
        move || std::thread::sleep(duration),
        move || Box::pin(tokio::time::sleep(duration)),
    )
    .await
}
```

Using `std`, `async-std` or `tokio` dynamically:

```rust
use async_std_if::{Std, Time, Tokio};

<Std as Time>::sleep(Duration::from_millis(100)).get();    // Synchronous!
<Tokio as Time>::sleep(Duration::from_millis(100)).await;  // Asynchronous!
```
