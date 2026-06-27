//! Derive macros for `axeyum-property`.

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{Data, DeriveInput, Fields, Generics, parse_macro_input, parse_quote};

/// Derives `axeyum_property::Symbolic` for structs.
///
/// Named fields use `Property::symbolic_struct`, so a field `amount` on an
/// input named `transfer` declares the Axeyum symbol `transfer.amount`. Tuple
/// fields use numeric suffixes such as `input.0`.
#[proc_macro_derive(Symbolic)]
pub fn derive_symbolic(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match expand_symbolic(&input) {
        Ok(tokens) => tokens.into(),
        Err(error) => error.to_compile_error().into(),
    }
}

fn expand_symbolic(input: &DeriveInput) -> syn::Result<proc_macro2::TokenStream> {
    let Data::Struct(data) = &input.data else {
        return Err(syn::Error::new_spanned(
            input,
            "Symbolic can only be derived for structs",
        ));
    };

    match &data.fields {
        Fields::Named(fields) => Ok(expand_named_struct(input, fields)),
        Fields::Unnamed(fields) => Ok(expand_tuple_struct(input, fields)),
        Fields::Unit => Ok(expand_unit_struct(input)),
    }
}

fn generics_with_symbolic_bounds<'a>(
    generics: &'a Generics,
    field_types: impl IntoIterator<Item = &'a syn::Type>,
) -> Generics {
    let mut generics = generics.clone();
    let where_clause = generics.make_where_clause();
    for ty in field_types {
        where_clause
            .predicates
            .push(parse_quote!(#ty: ::axeyum_property::Symbolic<Concrete = #ty>));
    }
    generics
}

fn expand_named_struct(input: &DeriveInput, fields: &syn::FieldsNamed) -> proc_macro2::TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let expr_name = format_ident!("__Axeyum{}SymbolicExpr", name);
    let field_types = fields.named.iter().map(|field| &field.ty);
    let bounded_generics = generics_with_symbolic_bounds(&input.generics, field_types);
    let (impl_generics, ty_generics, where_clause) = bounded_generics.split_for_impl();

    let expr_fields = fields.named.iter().map(|field| {
        let vis = &field.vis;
        let ident = field.ident.as_ref().expect("named field has ident");
        let ty = &field.ty;
        quote!(#vis #ident: <#ty as ::axeyum_property::Symbolic>::Expr)
    });

    let symbolic_fields = fields.named.iter().map(|field| {
        let ident = field.ident.as_ref().expect("named field has ident");
        let ty = &field.ty;
        let field_name = ident.to_string();
        quote!(#ident: fields.field::<#ty>(#field_name)?)
    });

    let concrete_bindings = fields.named.iter().map(|field| {
        let ident = field.ident.as_ref().expect("named field has ident");
        let ty = &field.ty;
        quote! {
            let Some(#ident) =
                <#ty as ::axeyum_property::Symbolic>::concrete(&expr.#ident, model)?
            else {
                return Ok(None);
            };
        }
    });

    let concrete_fields = fields.named.iter().map(|field| {
        let ident = field.ident.as_ref().expect("named field has ident");
        quote!(#ident)
    });

    quote! {
        #[allow(non_camel_case_types, missing_docs)]
        #vis struct #expr_name #impl_generics #where_clause {
            #(#expr_fields,)*
        }

        impl #impl_generics ::axeyum_property::Symbolic for #name #ty_generics #where_clause {
            type Expr = #expr_name #ty_generics;
            type Concrete = Self;

            fn symbolic(
                property: &mut ::axeyum_property::Property,
                name: &str,
            ) -> Result<Self::Expr, ::axeyum_property::PropertyError> {
                property.symbolic_struct(name, |fields| {
                    Ok(#expr_name {
                        #(#symbolic_fields,)*
                    })
                })
            }

            fn concrete(
                expr: &Self::Expr,
                model: &::axeyum_property::Model,
            ) -> Result<Option<Self::Concrete>, ::axeyum_property::PropertyError> {
                #(#concrete_bindings)*
                Ok(Some(Self {
                    #(#concrete_fields,)*
                }))
            }
        }
    }
}

fn expand_tuple_struct(
    input: &DeriveInput,
    fields: &syn::FieldsUnnamed,
) -> proc_macro2::TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let expr_name = format_ident!("__Axeyum{}SymbolicExpr", name);
    let field_types = fields.unnamed.iter().map(|field| &field.ty);
    let bounded_generics = generics_with_symbolic_bounds(&input.generics, field_types);
    let (impl_generics, ty_generics, where_clause) = bounded_generics.split_for_impl();

    let expr_fields = fields.unnamed.iter().map(|field| {
        let vis = &field.vis;
        let ty = &field.ty;
        quote!(#vis <#ty as ::axeyum_property::Symbolic>::Expr)
    });

    let symbolic_fields = fields.unnamed.iter().enumerate().map(|(i, field)| {
        let ty = &field.ty;
        let field_name = i.to_string();
        quote!(<#ty as ::axeyum_property::Symbolic>::symbolic(
            property,
            &format!("{name}.{}", #field_name),
        )?)
    });

    let concrete_bindings = fields.unnamed.iter().enumerate().map(|(i, field)| {
        let binding = format_ident!("field_{i}");
        let index = syn::Index::from(i);
        let ty = &field.ty;
        quote! {
            let Some(#binding) =
                <#ty as ::axeyum_property::Symbolic>::concrete(&expr.#index, model)?
            else {
                return Ok(None);
            };
        }
    });

    let concrete_fields = (0..fields.unnamed.len()).map(|i| {
        let binding = format_ident!("field_{i}");
        quote!(#binding)
    });

    quote! {
        #[allow(non_camel_case_types, missing_docs)]
        #vis struct #expr_name #impl_generics(
            #(#expr_fields,)*
        ) #where_clause;

        impl #impl_generics ::axeyum_property::Symbolic for #name #ty_generics #where_clause {
            type Expr = #expr_name #ty_generics;
            type Concrete = Self;

            fn symbolic(
                property: &mut ::axeyum_property::Property,
                name: &str,
            ) -> Result<Self::Expr, ::axeyum_property::PropertyError> {
                Ok(#expr_name(
                    #(#symbolic_fields,)*
                ))
            }

            fn concrete(
                expr: &Self::Expr,
                model: &::axeyum_property::Model,
            ) -> Result<Option<Self::Concrete>, ::axeyum_property::PropertyError> {
                #(#concrete_bindings)*
                Ok(Some(Self(
                    #(#concrete_fields,)*
                )))
            }
        }
    }
}

fn expand_unit_struct(input: &DeriveInput) -> proc_macro2::TokenStream {
    let name = &input.ident;
    let bounded_generics = input.generics.clone();
    let (impl_generics, ty_generics, where_clause) = bounded_generics.split_for_impl();

    quote! {
        impl #impl_generics ::axeyum_property::Symbolic for #name #ty_generics #where_clause {
            type Expr = ();
            type Concrete = Self;

            fn symbolic(
                _property: &mut ::axeyum_property::Property,
                _name: &str,
            ) -> Result<Self::Expr, ::axeyum_property::PropertyError> {
                Ok(())
            }

            fn concrete(
                _expr: &Self::Expr,
                _model: &::axeyum_property::Model,
            ) -> Result<Option<Self::Concrete>, ::axeyum_property::PropertyError> {
                Ok(Some(Self))
            }
        }
    }
}
