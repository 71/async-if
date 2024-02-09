#![macro_use]

/// Maps a crate name to its corresponding marker type.
macro_rules! AsyncTraitType {
    ( "std" ) => {
        $crate::Std
    };
    ( "async-std" ) => {
        $crate::AsyncStd
    };
    ( "tokio" ) => {
        $crate::Tokio
    };
}

/// Maps a crate name to its corresponding expression.
macro_rules! async_trait_find_expr {
    ( "std", "std" => $impl: expr, $($rest_marker: tt => $rest: expr,)* ) => {
        $impl
    };
    ( "async-std", "async-std" => $impl: expr, $($rest_marker: tt => $rest: expr,)* ) => {
        $impl
    };
    ( "tokio", "tokio" => $impl: expr, $($rest_marker: tt => $rest: expr,)* ) => {
        $impl
    };

    ( $cfg: tt, $_impl_marker: tt => $_impl: expr, $($rest_marker: tt => $rest: expr,)* ) => {
        async_trait_find_expr!($cfg, $($rest_marker => $rest,)*)
    };

    ( $cfg: tt, ) => {
        compile_error!("no implementation found for marker")
    };
}

/// Defines an `#[async_if]` trait and its implementations for different marker types.
macro_rules! async_trait {
    (
        $(#[$attr: meta])*
        pub trait $trait_name: ident {
            $(
                $(#[$fn_attr: meta])*
                async fn $fn_name: ident ( $($param_name: ident: $param_ty: ty),* ) $(-> $return_type: ty)? {
                    match Self {
                        $($match_cfg: tt => $impl: expr,)*
                    }
                }
            )*
        }

        impl for;
    ) => {
        $(#[$attr])*
        #[$crate::async_if::async_if(Self::IsAsync)]
        pub trait $trait_name {
            /// Whether methods provided by this implementation are asynchronous.
            type IsAsync: $crate::async_if::IsAsync;

            $(
                $(#[$fn_attr])*
                async fn $fn_name($($param_name: $param_ty),*) $(-> $return_type)?;
            )*
        }
    };

    (
        $(#[$attr: meta])*
        pub trait $trait_name: ident {
            $(
                $(#[$fn_attr: meta])*
                async fn $fn_name: ident ( $($param_name: ident: $param_ty: ty),* ) $(-> $return_type: ty)? {
                    match Self {
                        $($match_cfg: tt => $impl: expr,)*
                    }
                }
            )*
        }

        impl for $cfg: tt $(if $more_cfg: literal)? $(,$cfg_rest: tt $(if $more_cfg_rest: literal)?)*;
    ) => {
        async_trait! {
            $(#[$attr])*
            pub trait $trait_name {
                $(
                    $(#[$fn_attr])*
                    async fn $fn_name ( $($param_name: $param_ty),* ) $(-> $return_type)? {
                        match Self {
                            $($match_cfg => $impl,)*
                        }
                    }
                )*
            }

            impl for $($cfg_rest $(if $more_cfg_rest)?),*;
        }

        #[cfg(feature = $cfg)]
        $(#[cfg(feature = $more_cfg)])?
        #[$crate::async_if::async_if(Self::IsAsync)]
        impl $trait_name for AsyncTraitType![$cfg] {
            type IsAsync =
                $crate::async_if::AsyncWhen<{<AsyncTraitType![$cfg]>::IS_ASYNC}>;

            $(
                async fn $fn_name($($param_name: $param_ty),*) $(-> $return_type)? {
                    async_trait_find_expr!($cfg, $($match_cfg => $impl,)*)
                }
            )*
        }
    };
}

/// Defines the given function and generates one `#[tokio::test]` test per type in `in (...)`.
#[cfg(test)]
macro_rules! test_all {
    ( async fn $test_name: ident <$ty_ident: ident: $ty: ident in ()> () $(-> $return_type: ty)? $body: block ) => {
        #[$crate::async_if::async_if($ty_ident::IsAsync)]
        async fn $test_name<$ty_ident: $ty>() $(-> $return_type)? $body
    };

    ( async fn $test_name: ident <$ty_ident: ident: $ty: ident in (Std $(,$rest: tt)*)> () $(-> $return_type: ty)? $body: block ) => {
        paste::paste! {
            #[cfg(feature = "std")]
            #[tokio::test]
            async fn [< $test_name _std >] () {
                use $crate::async_if::AsyncIf;

                // Ensure that the function does not yield with `.get()`.
                $test_name::<$crate::Std>().get()
            }
        }

        test_all! {
            async fn $test_name<$ty_ident: $ty in ($($rest),*)> () $(-> $return_type)? $body
        }
    };

    ( async fn $test_name: ident <$ty_ident: ident: $ty: ident in (AsyncStd $(,$rest: tt)*)> () $(-> $return_type: ty)? $body: block ) => {
        paste::paste! {
            #[cfg(feature = "async-std")]
            #[tokio::test]
            async fn [< $test_name _async_std >] () {
                $test_name::<$crate::AsyncStd>().await
            }
        }

        test_all! {
            async fn $test_name<$ty_ident: $ty in ($($rest),*)> () $(-> $return_type)? $body
        }
    };

    ( async fn $test_name: ident <$ty_ident: ident: $ty: ident in (Tokio $(,$rest: tt)*)> () $(-> $return_type: ty)? $body: block ) => {
        paste::paste! {
            #[cfg(feature = "tokio")]
            #[tokio::test]
            async fn [< $test_name _tokio >] () {
                $test_name::<$crate::Tokio>().await
            }
        }

        test_all! {
            async fn $test_name<$ty_ident: $ty in ($($rest),*)> () $(-> $return_type)? $body
        }
    };
}

#[cfg(not(test))]
macro_rules! test_all {
    ( async fn $test_name: ident <$ty_ident: ident: $ty: ident in ($($rest: tt),*)> () $(-> $return_type: ty)? $body: block ) => {};
}
