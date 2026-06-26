//! Derive macro for `axeyum_property::Symbolic`.
//!
//! `#[derive(Symbolic)]` on a struct whose every field is itself `Symbolic`
//! generates two things:
//!
//! 1. a **concrete companion struct** `<Name>Concrete` whose fields are the
//!    per-field `Symbolic::Concrete` types (so a counterexample is a fully
//!    typed value, not a tuple); and
//! 2. an `impl Symbolic for <Name>` that declares one fresh symbolic value per
//!    field (left-to-right) and lifts a model back into `<Name>Concrete`.
//!
//! This lifts the arity-3 tuple ceiling: any struct (named or tuple struct, any
//! field count) becomes a symbolic input type. The companion struct re-uses the
//! input's generics, so a `Point<'c> { x: Bv<'c, 32>, y: Bv<'c, 32> }` yields a
//! `PointConcrete { x: u128, y: u128 }`.
#![forbid(unsafe_code)]

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{Data, DeriveInput, Fields, Lifetime, parse_macro_input};

/// Derives `axeyum_property::Symbolic` for a struct of `Symbolic` fields.
///
/// Requires exactly one lifetime parameter (the `Ctx` borrow `'c` the handles
/// live for); extra const/type generics are forwarded unchanged. Enums and
/// unions are a clean compile error.
#[proc_macro_derive(Symbolic)]
pub fn derive_symbolic(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match expand(&input) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

fn expand(input: &DeriveInput) -> syn::Result<proc_macro2::TokenStream> {
    let name = &input.ident;
    let vis = &input.vis;

    let Data::Struct(data) = &input.data else {
        return Err(syn::Error::new_spanned(
            input,
            "#[derive(Symbolic)] supports only structs (whose fields are themselves Symbolic)",
        ));
    };

    // Find the single lifetime the symbolic handles borrow (`'c`). All handle
    // types (`Bv<'c, W>`, `Int<'c>`, ...) carry it; the derived impl needs it.
    let lifetimes: Vec<&Lifetime> = input.generics.lifetimes().map(|l| &l.lifetime).collect();
    if lifetimes.len() != 1 {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "#[derive(Symbolic)] requires exactly one lifetime parameter (the Ctx borrow, e.g. `'c`)",
        ));
    }
    let lt = lifetimes[0];

    // Non-lifetime generics (const widths, type params) are forwarded to both the
    // impl and the concrete companion struct.
    let const_params: Vec<_> = input.generics.const_params().collect();
    let type_params: Vec<_> = input.generics.type_params().collect();

    // Concrete companion struct: same name + `Concrete`, same non-lifetime
    // generics, each field replaced by its `Symbolic::Concrete`.
    let concrete_name = format_ident!("{}Concrete", name);

    let is_named = matches!(&data.fields, Fields::Named(_));
    let Fielded {
        concrete_field_defs,
        fresh_inits,
        lift_inits,
    } = collect_fields(input, &data.fields, vis, lt)?;

    // Generic param lists. `bound` adds the `: Symbolic<#lt>` trait bound on type
    // params; `def` keeps the const/type *definition* form (`const N: usize`)
    // vs. the *use* form (`N`). The concrete companion re-uses the input's
    // lifetime (its `Concrete` field types are written through `Symbolic<#lt>`),
    // with a `PhantomData<&#lt ()>` marker so the lifetime is actually used.
    let generics = |def: bool, bound: bool| {
        let tps = type_params.iter().map(|p| {
            let id = &p.ident;
            if bound {
                quote! { #id: ::axeyum_property::Symbolic<#lt> }
            } else {
                quote! { #id }
            }
        });
        let cps = const_params.iter().map(|p| {
            let id = &p.ident;
            let tyc = &p.ty;
            if def {
                quote! { const #id: #tyc }
            } else {
                quote! { #id }
            }
        });
        quote! { #lt, #(#tps,)* #(#cps,)* }
    };
    let concrete_generics = generics(true, false);
    let concrete_use_generics = generics(false, false);
    let impl_generics = generics(true, true);
    let self_use_generics = generics(false, false);
    let marker_ty = quote! { ::core::marker::PhantomData<& #lt ()> };

    let concrete_struct = if is_named {
        quote! {
            #[derive(Debug, Clone, PartialEq)]
            #vis struct #concrete_name < #concrete_generics > {
                #(#concrete_field_defs,)*
                #[doc(hidden)]
                pub __axeyum_marker: #marker_ty,
            }
        }
    } else {
        quote! {
            #[derive(Debug, Clone, PartialEq)]
            #vis struct #concrete_name < #concrete_generics > ( #(#concrete_field_defs,)* #[doc(hidden)] pub #marker_ty );
        }
    };

    let fresh_body = if is_named {
        quote! { Self { #(#fresh_inits,)* } }
    } else {
        quote! { Self( #(#fresh_inits,)* ) }
    };
    let lift_body = if is_named {
        quote! { #concrete_name { #(#lift_inits,)* __axeyum_marker: ::core::marker::PhantomData } }
    } else {
        quote! { #concrete_name( #(#lift_inits,)* ::core::marker::PhantomData ) }
    };

    Ok(quote! {
        #concrete_struct

        impl < #impl_generics > ::axeyum_property::Symbolic<#lt> for #name < #self_use_generics > {
            type Concrete = #concrete_name < #concrete_use_generics >;

            fn fresh(ctx: & #lt ::axeyum_property::Ctx, slots: &mut ::std::vec::Vec<::axeyum_property::Slot>) -> Self {
                #fresh_body
            }

            fn lift(leaves: &mut impl ::core::iter::Iterator<Item = ::axeyum_property::Lifted>) -> Self::Concrete {
                #lift_body
            }
        }
    })
}

/// The per-field token fragments, in declaration order: the concrete-struct
/// field definitions, the `fresh` initialisers, and the `lift` initialisers.
struct Fielded {
    concrete_field_defs: Vec<proc_macro2::TokenStream>,
    fresh_inits: Vec<proc_macro2::TokenStream>,
    lift_inits: Vec<proc_macro2::TokenStream>,
}

/// Builds, for each field of `fields` (in order), its concrete-type definition,
/// `Symbolic::fresh` initialiser, and `Symbolic::lift` initialiser.
fn collect_fields(
    input: &DeriveInput,
    fields: &Fields,
    vis: &syn::Visibility,
    lt: &Lifetime,
) -> syn::Result<Fielded> {
    let field_iter: Vec<(Option<syn::Ident>, &syn::Type)> = match fields {
        Fields::Named(f) => f
            .named
            .iter()
            .map(|fld| (fld.ident.clone(), &fld.ty))
            .collect(),
        Fields::Unnamed(f) => f.unnamed.iter().map(|fld| (None, &fld.ty)).collect(),
        Fields::Unit => {
            return Err(syn::Error::new_spanned(
                input,
                "#[derive(Symbolic)] needs at least one field; unit structs carry no symbolic input",
            ));
        }
    };

    let mut out = Fielded {
        concrete_field_defs: Vec::new(),
        fresh_inits: Vec::new(),
        lift_inits: Vec::new(),
    };
    for (ident, ty) in &field_iter {
        let concrete_ty = quote! { <#ty as ::axeyum_property::Symbolic<#lt>>::Concrete };
        let fresh = quote! { <#ty as ::axeyum_property::Symbolic<#lt>>::fresh(ctx, slots) };
        let lift = quote! { <#ty as ::axeyum_property::Symbolic<#lt>>::lift(leaves) };
        if let Some(id) = ident {
            out.concrete_field_defs
                .push(quote! { #vis #id: #concrete_ty });
            out.fresh_inits.push(quote! { #id: #fresh });
            out.lift_inits.push(quote! { #id: #lift });
        } else {
            out.concrete_field_defs.push(quote! { #vis #concrete_ty });
            out.fresh_inits.push(fresh);
            out.lift_inits.push(lift);
        }
    }
    Ok(out)
}
