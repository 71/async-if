use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse::Parse, spanned::Spanned, visit_mut::VisitMut};

/// Attribute options available in [`async_if`].
///
/// See [`test_parse_attr()`] for example syntax.
struct Attr {
    condition: syn::Type,
    alloc_with: Option<syn::Expr>,
    by_ref: bool,
}

/// Attribute options available in [`async_when`].
///
/// See [`test_parse_expr_attr()`] for example syntax.
struct ExprAttr(Attr);

impl Attr {
    fn parse_as(input: syn::parse::ParseStream, is_expr: bool) -> syn::Result<Self> {
        let condition = if is_expr {
            let expr = input.parse::<syn::Expr>()?;

            syn::parse_quote! { ::async_if::AsyncWhen<{ #expr }> }
        } else {
            input.parse()?
        };
        let mut alloc_with = None;

        if input.parse::<Option<syn::Token![,]>>().is_ok() {
            let meta = input.parse_terminated(syn::Meta::parse, syn::Token![,])?;

            for meta in meta {
                match meta {
                    syn::Meta::Path(path) if path.is_ident("alloc_with_box") => {
                        alloc_with = Some(syn::parse_quote! { &::async_if::AllocFutureWithBox });
                    }
                    syn::Meta::NameValue(name_value) if name_value.path.is_ident("alloc_with") => {
                        alloc_with = Some(name_value.value);
                    }
                    meta => return Err(syn::Error::new(meta.span(), "unknown attribute argument")),
                }
            }
        }

        Ok(Self {
            condition,
            alloc_with,
            by_ref: false,
        })
    }

    fn for_block(by_ref: bool) -> Self {
        Self {
            condition: syn::Type::Infer(syn::TypeInfer {
                underscore_token: syn::token::Underscore::default(),
            }),
            alloc_with: None,
            by_ref,
        }
    }

    #[cfg(test)]
    fn from_attr(attr: syn::Attribute) -> Self {
        if attr.path().is_ident("async_if") {
            attr.parse_args().unwrap()
        } else if attr.path().is_ident("async_when") {
            attr.parse_args::<ExprAttr>().unwrap().0
        } else {
            panic!("cannot parse attribute: {}", attr.to_token_stream());
        }
    }
}

impl Parse for Attr {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Attr::parse_as(input, false)
    }
}

impl Parse for ExprAttr {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Attr::parse_as(input, true).map(Self)
    }
}

#[test]
fn test_parse_attr() {
    let attr: Attr = syn::parse_quote! { A };

    assert_eq!(
        attr.condition.to_token_stream().to_string(),
        quote! { A }.to_string(),
    );
    assert!(
        attr.alloc_with.is_none(),
        "{}",
        attr.alloc_with.to_token_stream().to_string(),
    );

    let attr: Attr = syn::parse_quote! { Other::Scope, alloc_with = bump };

    assert_eq!(
        attr.condition.to_token_stream().to_string(),
        quote! { Other::Scope }.to_string(),
    );
    assert_eq!(
        attr.alloc_with.unwrap().to_token_stream().to_string(),
        quote! { bump }.to_string(),
    );

    let attr: Attr = syn::parse_quote! { Other::Scope, alloc_with_box };

    assert_eq!(
        attr.condition.to_token_stream().to_string(),
        quote! { Other::Scope }.to_string(),
    );
    assert_eq!(
        attr.alloc_with.unwrap().to_token_stream().to_string(),
        quote! { &::async_if::AllocFutureWithBox }.to_string(),
    );
}

#[test]
fn test_parse_expr_attr() {
    let ExprAttr(attr) = syn::parse_quote! { super::is_async(), alloc_with = bump };

    assert_eq!(
        attr.condition.to_token_stream().to_string(),
        quote! { ::async_if::AsyncWhen<{ super::is_async() }> }.to_string(),
    );
    assert_eq!(
        attr.alloc_with.unwrap().to_token_stream().to_string(),
        quote! { bump }.to_string(),
    );
}

/// AST [`Visitor`](VisitMut) which appends all seen lifetimes to a [`proc_macro2::TokenStream`].
///
/// See [`test_collect_lifetimes()`] for an example.
struct CollectLifetimes {
    lifetimes: proc_macro2::TokenStream,
}

impl VisitMut for CollectLifetimes {
    fn visit_type_reference_mut(&mut self, type_ref: &mut syn::TypeReference) {
        if type_ref.lifetime.is_none() {
            self.lifetimes.extend(quote! { + '_ });
        }

        syn::visit_mut::visit_type_reference_mut(self, type_ref);
    }

    fn visit_lifetime_mut(&mut self, lifetime: &mut syn::Lifetime) {
        self.lifetimes.extend(quote! { + #lifetime });
    }
}

#[test]
fn test_collect_lifetimes() {
    let mut collector = CollectLifetimes {
        lifetimes: proc_macro2::TokenStream::new(),
    };

    collector.visit_type_mut(&mut syn::parse_quote! { &mut A<'a, B<&'b C>, D<'_>> });

    assert_eq!(
        collector.lifetimes.to_string(),
        quote! { + '_ + 'a + 'b + '_ }.to_string(),
    );
}

/// Expands the body of a function or closure, or the block given to [`async_ref`] / [`async_move`].
///
/// See [`test_expand_body()`] for an example.
fn expand_body(attr: &Attr, body: &mut syn::Block) {
    let inferred_is_async_ident = syn::Ident::new("is_async", proc_macro2::Span::mixed_site());

    struct Visitor<'a> {
        inferred_is_async_ident: &'a syn::Ident,
    }

    impl VisitMut for Visitor<'_> {
        fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
            match expr {
                syn::Expr::Async(_) | syn::Expr::Closure(_) => {
                    // Do not visit inner async blocks or closures, which should instead get their
                    // own attribute.
                }
                syn::Expr::Await(syn::ExprAwait { base, .. }) => {
                    self.visit_expr_mut(&mut *base);

                    let inferred_is_async_ident = &self.inferred_is_async_ident;

                    *base.as_mut() = syn::parse_quote! {
                        ::async_if::infer_with(#base, #inferred_is_async_ident)
                    };
                }
                _ => syn::visit_mut::visit_expr_mut(self, expr),
            }
        }

        fn visit_item_fn_mut(&mut self, _: &mut syn::ItemFn) {
            // Do not visit functions recursively as they will be processed if they are annotated
            // with an attribute.
        }

        fn visit_impl_item_fn_mut(&mut self, _: &mut syn::ImplItemFn) {
            // Do not visit functions recursively as they will be processed if they are annotated
            // with an attribute.
        }
    }

    Visitor {
        inferred_is_async_ident: &inferred_is_async_ident,
    }
    .visit_block_mut(body);

    let move_token = (!attr.by_ref).then(|| syn::Token![move](proc_macro2::Span::call_site()));

    *body = syn::parse_quote! {{
        let #inferred_is_async_ident = ::core::marker::PhantomData;
        let _ = #inferred_is_async_ident; // Avoid "unused variable" warnings.

        unsafe {
            ::async_if::PossiblySyncFuture::infer_unchecked(async #move_token #body, #inferred_is_async_ident)
        }
    }};

    if let Attr {
        alloc_with: Some(alloc_with),
        condition,
        by_ref: _,
    } = attr
    {
        *body = syn::parse_quote! {{
            ::async_if::alloc_future_if::<#condition, _, _>(#alloc_with, #body)
        }}
    }
}

#[cfg(test)]
fn expand_body_for_test(attr: syn::Attribute, mut body: syn::Block) -> syn::Block {
    expand_body(&Attr::from_attr(attr), &mut body);
    body
}

#[test]
fn test_expand_body() {
    assert_eq!(
        expand_body_for_test(
            syn::parse_quote! { #[async_if(A)] },
            syn::parse_quote! { { foo().await; bar().await } },
        )
        .to_token_stream()
        .to_string(),
        quote! {{
            let is_async = ::core::marker::PhantomData;
            let _ = is_async;

            unsafe {
                ::async_if::PossiblySyncFuture::infer_unchecked(
                    async move {
                        ::async_if::infer_with(foo(), is_async).await;
                        ::async_if::infer_with(bar(), is_async).await
                    },
                    is_async
                )
            }
        }}
        .to_string(),
    );

    assert_eq!(
        expand_body_for_test(
            syn::parse_quote! { #[async_when(CONST, alloc_with = bump)] },
            syn::parse_quote! { { (async move { v.await }).await; } },
        )
        .to_token_stream()
        .to_string(),
        quote! {{
            ::async_if::alloc_future_if::<::async_if::AsyncWhen<{ CONST }>, _, _>(
                bump,
                {
                    let is_async = ::core::marker::PhantomData;
                    let _ = is_async;

                    unsafe {
                        ::async_if::PossiblySyncFuture::infer_unchecked(
                            async move {
                                ::async_if::infer_with((async move { v.await }), is_async).await;
                            },
                            is_async
                        )
                    }
                }
            )
        }}
        .to_string(),
    );
}

/// Expands the signature of a function.
///
/// See [`test_expand_signature()`] for an example.
fn expand_signature(attr: &Attr, signature: &mut syn::Signature) -> syn::Result<()> {
    if signature.asyncness.is_none() {
        return Err(syn::Error::new_spanned(
            signature.fn_token,
            "function must be async",
        ));
    }

    let output_type = match std::mem::replace(&mut signature.output, syn::ReturnType::Default) {
        syn::ReturnType::Default => Box::new(syn::parse_quote! { () }),
        syn::ReturnType::Type(_, ty) => ty,
    };

    let captures_lifetimes = {
        let mut collector = CollectLifetimes {
            lifetimes: proc_macro2::TokenStream::new(),
        };

        collector.visit_signature_mut(signature);
        collector.lifetimes
    };

    let Attr { condition, .. } = &attr;

    signature.asyncness = None;
    signature.output = syn::parse_quote! { -> impl ::async_if::AsyncIf<#condition, Output = #output_type> #captures_lifetimes };

    Ok(())
}

#[cfg(test)]
fn expand_signature_for_test(attr: syn::Attribute, mut sig: syn::Signature) -> syn::Signature {
    expand_signature(&Attr::from_attr(attr), &mut sig).unwrap();
    sig
}

#[test]
fn test_expand_signature() {
    assert_eq!(
        expand_signature_for_test(
            syn::parse_quote! { #[async_if(A)] },
            syn::parse_quote! { async fn foo() -> u32 }
        )
        .to_token_stream()
        .to_string(),
        quote! { fn foo() -> impl ::async_if::AsyncIf<A, Output = u32> }.to_string(),
    );

    assert_eq!(
        expand_signature_for_test(
            syn::parse_quote! { #[async_when(Some::VALUE)] },
            syn::parse_quote! { async fn bar<'a, 'b: 'a>(&self, x: &'a B<'b>) -> Bar }
        )
        .to_token_stream()
        .to_string(),
        quote! {
            fn bar<'a, 'b: 'a>(&self, x: &'a B<'b>) -> impl ::async_if::AsyncIf<
                ::async_if::AsyncWhen<{ Some::VALUE }>, Output = Bar > + 'a + 'b + 'a + '_ + 'a + 'b
        }
        .to_string(),
    );
}

/// Expands the signature and body of a function.
fn expand_fn_like(
    attr: &Attr,
    signature: &mut syn::Signature,
    body: &mut syn::Block,
) -> syn::Result<()> {
    expand_signature(attr, signature)?;
    expand_body(attr, body);

    Ok(())
}

/// Expands the tokens given to [`async_if`] or [`async_when`].
fn expand(attr_name: &'static str, attr: Attr, item: TokenStream) -> syn::Result<TokenStream> {
    let mut item = syn::parse(item)?;

    match &mut item {
        syn::Item::Fn(syn::ItemFn { sig, block, .. }) => {
            expand_fn_like(&attr, sig, &mut *block)?;
        }
        syn::Item::Impl(syn::ItemImpl { items, .. }) => {
            for impl_item in items {
                let syn::ImplItem::Fn(syn::ImplItemFn { sig, block, .. }) = impl_item else {
                    continue;
                };

                if sig.asyncness.is_none() {
                    continue;
                }

                expand_fn_like(&attr, sig, block)?;
            }
        }
        syn::Item::Trait(syn::ItemTrait { items, .. }) => {
            for trait_item in items {
                let syn::TraitItem::Fn(syn::TraitItemFn { sig, default, .. }) = trait_item else {
                    continue;
                };

                if sig.asyncness.is_none() {
                    continue;
                }

                expand_signature(&attr, sig)?;

                if let Some(body) = default {
                    expand_body(&attr, body);
                }
            }
        }
        _ => {
            return Err(syn::Error::new(
                item.span(),
                format!(
                    "attribute #[{attr_name}] can only be applied to functions, impls and traits",
                ),
            ))
        }
    }

    Ok(item.into_token_stream().into())
}

#[proc_macro_attribute]
pub fn async_if(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = syn::parse_macro_input!(attr);

    match expand("async_if", attr, item) {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error().into(),
    }
}

#[proc_macro_attribute]
pub fn async_when(attr: TokenStream, item: TokenStream) -> TokenStream {
    let ExprAttr(attr) = syn::parse_macro_input!(attr);

    match expand("async_when", attr, item) {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error().into(),
    }
}

#[proc_macro]
pub fn async_move(tokens: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(tokens);
    let mut body = syn::parse_quote! { { #tokens } };

    expand_body(&Attr::for_block(false), &mut body);

    body.into_token_stream().into()
}

#[proc_macro]
pub fn async_ref(tokens: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(tokens);
    let mut body = syn::parse_quote! { { #tokens } };

    expand_body(&Attr::for_block(true), &mut body);

    body.into_token_stream().into()
}
