//! Canonical imported-declaration identity (ADR-0350).

use std::collections::BTreeMap;

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, Kernel, LevelId, LevelNode, Lit, NameId, NameNode,
    QuotKind, ReducibilityHint,
};
use sha2::{Digest, Sha256};

type Hash = [u8; 32];

const NAME_DOMAIN: &str = "axeyum.lean.name.v1";
const LEVEL_DOMAIN: &str = "axeyum.lean.level.v1";
const EXPR_DOMAIN: &str = "axeyum.lean.expr.v1";
const DECL_DOMAIN: &str = "axeyum.lean.declaration.v1";
const DEPENDENCY_DOMAIN: &str = "axeyum.lean.direct-dependencies.v1";

/// Stable imported-declaration kind label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclarationKind {
    /// An asserted constant with no body.
    Axiom,
    /// A reducible definition.
    Definition,
    /// A theorem with a checked proof body.
    Theorem,
    /// An opaque constant with a checked body.
    Opaque,
    /// An inductive family generated and checked by the kernel.
    Inductive,
    /// A checked inductive constructor.
    Constructor,
    /// A generated checked recursor and its reduction rules.
    Recursor,
    /// One member of Lean's privileged fixed quotient package.
    Quotient,
}

impl DeclarationKind {
    const fn tag(self) -> u8 {
        match self {
            Self::Axiom => 0,
            Self::Definition => 1,
            Self::Theorem => 2,
            Self::Opaque => 3,
            Self::Inductive => 4,
            Self::Constructor => 5,
            Self::Recursor => 6,
            Self::Quotient => 7,
        }
    }
}

/// TL0.4-compatible identity for one imported axiom.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AxiomIdentity {
    /// Exact displayed hierarchical declaration name.
    pub name: String,
    /// SHA-256 of the UTF-8 displayed name.
    pub name_sha256: String,
    /// SHA-256 of `Kernel::render_lean(declaration.ty())`, matching the TL0.4
    /// axiom-ledger type identity.
    pub type_sha256: String,
}

/// One direct dependency bound to the dependency's structural content.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclarationDependencyIdentity {
    /// Exact displayed hierarchical dependency name.
    pub name: String,
    /// Structural content SHA-256 of the admitted dependency declaration.
    pub content_sha256: String,
}

/// Canonical identity for one independently admitted declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclarationIdentity {
    /// Exact displayed hierarchical declaration name.
    pub name: String,
    /// Stable declaration variant.
    pub kind: DeclarationKind,
    /// Domain-separated structural SHA-256 of this declaration's complete
    /// checked content.
    pub content_sha256: String,
    /// Domain-separated SHA-256 of the sorted direct-dependency name/content
    /// bindings.
    pub dependency_sha256: String,
    /// Sorted, deduplicated direct-dependency bindings.
    pub dependencies: Vec<DeclarationDependencyIdentity>,
}

pub(crate) fn build_identity_manifest(
    kernel: &Kernel,
) -> Result<(Vec<AxiomIdentity>, Vec<DeclarationIdentity>), String> {
    let mut builder = IdentityBuilder::new(kernel);
    let mut declarations: Vec<_> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| declaration)
        .collect();
    declarations.sort_by_cached_key(|declaration| canonical_name_bytes(kernel, declaration.name()));

    let mut content_by_name = BTreeMap::new();
    for declaration in &declarations {
        let digest = builder.declaration_digest(declaration)?;
        content_by_name.insert(declaration.name(), digest);
    }

    let mut axioms = Vec::new();
    let mut identities = Vec::with_capacity(declarations.len());
    for declaration in declarations {
        let name = kernel.display_name(declaration.name()).to_string();
        let content = *content_by_name
            .get(&declaration.name())
            .ok_or_else(|| format!("missing own content digest for {name}"))?;
        if matches!(declaration, Declaration::Axiom { .. }) {
            axioms.push(AxiomIdentity {
                name: name.clone(),
                name_sha256: hex(&plain_sha256(name.as_bytes())),
                type_sha256: hex(&plain_sha256(
                    kernel.render_lean(declaration.ty()).as_bytes(),
                )),
            });
        }

        let dependency_names = builder.direct_dependencies(declaration);
        let mut dependency_hasher = CanonicalHasher::new(DEPENDENCY_DOMAIN);
        dependency_hasher.put_len(dependency_names.len());
        let mut dependencies = Vec::with_capacity(dependency_names.len());
        for dependency_name in dependency_names {
            let dependency_display = kernel.display_name(dependency_name).to_string();
            let dependency_content = *content_by_name.get(&dependency_name).ok_or_else(|| {
                format!("{name} references missing declaration {dependency_display}")
            })?;
            dependency_hasher.put_hash(builder.name_digest(dependency_name));
            dependency_hasher.put_hash(dependency_content);
            dependencies.push(DeclarationDependencyIdentity {
                name: dependency_display,
                content_sha256: hex(&dependency_content),
            });
        }
        identities.push(DeclarationIdentity {
            name,
            kind: declaration_kind(declaration),
            content_sha256: hex(&content),
            dependency_sha256: hex(&dependency_hasher.finish()),
            dependencies,
        });
    }
    Ok((axioms, identities))
}

struct IdentityBuilder<'kernel> {
    kernel: &'kernel Kernel,
    name_cache: Vec<Option<Hash>>,
    level_cache: Vec<Option<Hash>>,
    expression_cache: Vec<Option<Hash>>,
}

impl<'kernel> IdentityBuilder<'kernel> {
    fn new(kernel: &'kernel Kernel) -> Self {
        Self {
            kernel,
            name_cache: Vec::new(),
            level_cache: Vec::new(),
            expression_cache: Vec::new(),
        }
    }

    fn name_digest(&mut self, name: NameId) -> Hash {
        if let Some(digest) = get_cached(&self.name_cache, name.index()) {
            return digest;
        }
        let bytes = canonical_name_bytes(self.kernel, name);
        let mut hasher = CanonicalHasher::new(NAME_DOMAIN);
        hasher.put_bytes(&bytes);
        let digest = hasher.finish();
        set_cached(&mut self.name_cache, name.index(), digest);
        digest
    }

    fn level_digest(&mut self, level: LevelId) -> Hash {
        if let Some(digest) = get_cached(&self.level_cache, level.index()) {
            return digest;
        }
        let node = self.kernel.level_node(level).clone();
        let mut hasher = CanonicalHasher::new(LEVEL_DOMAIN);
        match node {
            LevelNode::Zero => hasher.put_u8(0),
            LevelNode::Succ(prior) => {
                hasher.put_u8(1);
                let child = self.level_digest(prior);
                hasher.put_hash(child);
            }
            LevelNode::Max(left, right) => {
                hasher.put_u8(2);
                let left = self.level_digest(left);
                let right = self.level_digest(right);
                hasher.put_hash(left);
                hasher.put_hash(right);
            }
            LevelNode::IMax(left, right) => {
                hasher.put_u8(3);
                let left = self.level_digest(left);
                let right = self.level_digest(right);
                hasher.put_hash(left);
                hasher.put_hash(right);
            }
            LevelNode::Param(name) => {
                hasher.put_u8(4);
                let name = self.name_digest(name);
                hasher.put_hash(name);
            }
        }
        let digest = hasher.finish();
        set_cached(&mut self.level_cache, level.index(), digest);
        digest
    }

    fn expression_digest(&mut self, root: ExprId) -> Result<Hash, String> {
        if let Some(digest) = get_cached(&self.expression_cache, root.index()) {
            return Ok(digest);
        }
        let mut stack = vec![(root, false)];
        while let Some((expression, expanded)) = stack.pop() {
            if get_cached(&self.expression_cache, expression.index()).is_some() {
                continue;
            }
            if !expanded {
                stack.push((expression, true));
                for child in expression_children(self.kernel.expr_node(expression)) {
                    if get_cached(&self.expression_cache, child.index()).is_none() {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            let digest = self.hash_expression_node(self.kernel.expr_node(expression).clone())?;
            set_cached(&mut self.expression_cache, expression.index(), digest);
        }
        get_cached(&self.expression_cache, root.index())
            .ok_or_else(|| format!("expression {} was not hashed", root.index()))
    }

    fn hash_expression_node(&mut self, node: ExprNode) -> Result<Hash, String> {
        let mut hasher = CanonicalHasher::new(EXPR_DOMAIN);
        match node {
            ExprNode::BVar(index) => {
                hasher.put_u8(0);
                hasher.put_u32(index);
            }
            ExprNode::FVar(id) => {
                hasher.put_u8(1);
                hasher.put_u64(id);
            }
            ExprNode::Sort(level) => {
                hasher.put_u8(2);
                let level = self.level_digest(level);
                hasher.put_hash(level);
            }
            ExprNode::Const(name, levels) => {
                hasher.put_u8(3);
                let name = self.name_digest(name);
                hasher.put_hash(name);
                hasher.put_len(levels.len());
                for level in levels {
                    let level = self.level_digest(level);
                    hasher.put_hash(level);
                }
            }
            ExprNode::Proj(type_name, field_index, structure) => {
                hasher.put_u8(4);
                let type_name = self.name_digest(type_name);
                hasher.put_hash(type_name);
                hasher.put_u32(field_index);
                hasher.put_hash(self.cached_expression(structure)?);
            }
            ExprNode::App(function, argument) => {
                hasher.put_u8(5);
                hasher.put_hash(self.cached_expression(function)?);
                hasher.put_hash(self.cached_expression(argument)?);
            }
            ExprNode::Lam(name, ty, body, binder_info) => {
                hasher.put_u8(6);
                let name = self.name_digest(name);
                hasher.put_hash(name);
                hasher.put_hash(self.cached_expression(ty)?);
                hasher.put_hash(self.cached_expression(body)?);
                hasher.put_u8(binder_info_tag(binder_info));
            }
            ExprNode::Pi(name, ty, body, binder_info) => {
                hasher.put_u8(7);
                let name = self.name_digest(name);
                hasher.put_hash(name);
                hasher.put_hash(self.cached_expression(ty)?);
                hasher.put_hash(self.cached_expression(body)?);
                hasher.put_u8(binder_info_tag(binder_info));
            }
            ExprNode::Let(name, ty, value, body) => {
                hasher.put_u8(8);
                let name = self.name_digest(name);
                hasher.put_hash(name);
                hasher.put_hash(self.cached_expression(ty)?);
                hasher.put_hash(self.cached_expression(value)?);
                hasher.put_hash(self.cached_expression(body)?);
            }
            ExprNode::Lit(Lit::Nat(value)) => {
                hasher.put_u8(9);
                hasher.put_bytes(value.to_string().as_bytes());
            }
            ExprNode::Lit(Lit::Str(value)) => {
                hasher.put_u8(10);
                hasher.put_bytes(value.as_bytes());
            }
        }
        Ok(hasher.finish())
    }

    fn cached_expression(&self, expression: ExprId) -> Result<Hash, String> {
        get_cached(&self.expression_cache, expression.index())
            .ok_or_else(|| format!("expression child {} was not hashed", expression.index()))
    }

    fn declaration_digest(&mut self, declaration: &Declaration) -> Result<Hash, String> {
        let mut hasher = CanonicalHasher::new(DECL_DOMAIN);
        hasher.put_u8(declaration_kind(declaration).tag());
        let name = self.name_digest(declaration.name());
        hasher.put_hash(name);
        hasher.put_len(declaration.uparams().len());
        for &parameter in declaration.uparams() {
            let parameter = self.name_digest(parameter);
            hasher.put_hash(parameter);
        }
        let ty = self.expression_digest(declaration.ty())?;
        hasher.put_hash(ty);
        match declaration {
            Declaration::Axiom { .. } => {}
            Declaration::Definition { value, hint, .. } => {
                let value = self.expression_digest(*value)?;
                hasher.put_hash(value);
                match hint {
                    ReducibilityHint::Opaque => hasher.put_u8(0),
                    ReducibilityHint::Regular(height) => {
                        hasher.put_u8(1);
                        hasher.put_u16(*height);
                    }
                    ReducibilityHint::Abbrev => hasher.put_u8(2),
                }
            }
            Declaration::Theorem { value, .. } | Declaration::Opaque { value, .. } => {
                let value = self.expression_digest(*value)?;
                hasher.put_hash(value);
            }
            Declaration::Inductive {
                num_params,
                num_indices,
                is_recursive,
                ctor_names,
                ..
            } => {
                hasher.put_u16(*num_params);
                hasher.put_u16(*num_indices);
                hasher.put_u8(u8::from(*is_recursive));
                hasher.put_len(ctor_names.len());
                for &constructor in ctor_names {
                    let constructor = self.name_digest(constructor);
                    hasher.put_hash(constructor);
                }
            }
            Declaration::Constructor {
                inductive,
                idx,
                num_fields,
                ..
            } => {
                let inductive = self.name_digest(*inductive);
                hasher.put_hash(inductive);
                hasher.put_u16(*idx);
                hasher.put_u16(*num_fields);
            }
            Declaration::Recursor {
                rec_rules,
                num_motives,
                num_minors,
                num_params,
                num_indices,
                ..
            } => {
                hasher.put_u16(*num_motives);
                hasher.put_u16(*num_minors);
                hasher.put_u16(*num_params);
                hasher.put_u16(*num_indices);
                hasher.put_len(rec_rules.len());
                for rule in rec_rules {
                    let constructor = self.name_digest(rule.ctor_name);
                    let value = self.expression_digest(rule.value)?;
                    hasher.put_hash(constructor);
                    hasher.put_u16(rule.num_fields);
                    hasher.put_hash(value);
                }
            }
            Declaration::Quotient { kind, .. } => {
                hasher.put_u8(match kind {
                    QuotKind::Type => 0,
                    QuotKind::Ctor => 1,
                    QuotKind::Lift => 2,
                    QuotKind::Ind => 3,
                });
            }
        }
        Ok(hasher.finish())
    }

    fn direct_dependencies(&self, declaration: &Declaration) -> Vec<NameId> {
        let mut dependencies = Vec::new();
        collect_expression_dependencies(self.kernel, declaration.ty(), &mut dependencies);
        if let Some(value) = declaration.value() {
            collect_expression_dependencies(self.kernel, value, &mut dependencies);
        }
        match declaration {
            Declaration::Inductive { ctor_names, .. } => {
                dependencies.extend(ctor_names.iter().copied());
            }
            Declaration::Constructor { inductive, .. } => dependencies.push(*inductive),
            Declaration::Recursor { rec_rules, .. } => {
                for rule in rec_rules {
                    dependencies.push(rule.ctor_name);
                    collect_expression_dependencies(self.kernel, rule.value, &mut dependencies);
                }
            }
            Declaration::Axiom { .. }
            | Declaration::Definition { .. }
            | Declaration::Theorem { .. }
            | Declaration::Opaque { .. }
            | Declaration::Quotient { .. } => {}
        }
        dependencies.retain(|dependency| *dependency != declaration.name());
        dependencies.sort_unstable();
        dependencies.dedup();
        dependencies.sort_by_cached_key(|name| canonical_name_bytes(self.kernel, *name));
        dependencies
    }
}

fn declaration_kind(declaration: &Declaration) -> DeclarationKind {
    match declaration {
        Declaration::Axiom { .. } => DeclarationKind::Axiom,
        Declaration::Definition { .. } => DeclarationKind::Definition,
        Declaration::Theorem { .. } => DeclarationKind::Theorem,
        Declaration::Opaque { .. } => DeclarationKind::Opaque,
        Declaration::Inductive { .. } => DeclarationKind::Inductive,
        Declaration::Constructor { .. } => DeclarationKind::Constructor,
        Declaration::Recursor { .. } => DeclarationKind::Recursor,
        Declaration::Quotient { .. } => DeclarationKind::Quotient,
    }
}

fn binder_info_tag(info: BinderInfo) -> u8 {
    match info {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

fn expression_children(node: &ExprNode) -> Vec<ExprId> {
    match node {
        ExprNode::Proj(_, _, structure) => vec![*structure],
        ExprNode::App(function, argument) => vec![*function, *argument],
        ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => vec![*ty, *body],
        ExprNode::Let(_, ty, value, body) => vec![*ty, *value, *body],
        ExprNode::BVar(_)
        | ExprNode::FVar(_)
        | ExprNode::Sort(_)
        | ExprNode::Const(_, _)
        | ExprNode::Lit(_) => Vec::new(),
    }
}

fn collect_expression_dependencies(kernel: &Kernel, root: ExprId, output: &mut Vec<NameId>) {
    let mut visited = Vec::<bool>::new();
    let mut stack = vec![root];
    while let Some(expression) = stack.pop() {
        if expression.index() >= visited.len() {
            visited.resize(expression.index() + 1, false);
        }
        if visited[expression.index()] {
            continue;
        }
        visited[expression.index()] = true;
        match kernel.expr_node(expression) {
            ExprNode::Const(name, _) => output.push(*name),
            ExprNode::Proj(type_name, _, structure) => {
                output.push(*type_name);
                stack.push(*structure);
            }
            ExprNode::App(function, argument) => {
                stack.push(*function);
                stack.push(*argument);
            }
            ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                stack.push(*ty);
                stack.push(*body);
            }
            ExprNode::Let(_, ty, value, body) => {
                stack.push(*ty);
                stack.push(*value);
                stack.push(*body);
            }
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => {}
        }
    }
}

fn canonical_name_bytes(kernel: &Kernel, mut name: NameId) -> Vec<u8> {
    enum Component {
        String(String),
        Number(u64),
    }

    let mut components = Vec::new();
    loop {
        match kernel.name_node(name) {
            NameNode::Anonymous => break,
            NameNode::Str(parent, component) => {
                components.push(Component::String(component.clone()));
                name = *parent;
            }
            NameNode::Num(parent, component) => {
                components.push(Component::Number(*component));
                name = *parent;
            }
        }
    }
    components.reverse();
    let mut output = Vec::new();
    output.extend_from_slice(&(components.len() as u64).to_be_bytes());
    for component in components {
        match component {
            Component::String(value) => {
                output.push(0);
                output.extend_from_slice(&(value.len() as u64).to_be_bytes());
                output.extend_from_slice(value.as_bytes());
            }
            Component::Number(value) => {
                output.push(1);
                output.extend_from_slice(&value.to_be_bytes());
            }
        }
    }
    output
}

struct CanonicalHasher(Sha256);

impl CanonicalHasher {
    fn new(domain: &str) -> Self {
        let mut hasher = Self(Sha256::new());
        hasher.put_bytes(domain.as_bytes());
        hasher
    }

    fn put_u8(&mut self, value: u8) {
        self.0.update([value]);
    }

    fn put_u16(&mut self, value: u16) {
        self.0.update(value.to_be_bytes());
    }

    fn put_u32(&mut self, value: u32) {
        self.0.update(value.to_be_bytes());
    }

    fn put_u64(&mut self, value: u64) {
        self.0.update(value.to_be_bytes());
    }

    fn put_len(&mut self, value: usize) {
        self.put_u64(value as u64);
    }

    fn put_bytes(&mut self, value: &[u8]) {
        self.put_len(value.len());
        self.0.update(value);
    }

    fn put_hash(&mut self, value: Hash) {
        self.0.update(value);
    }

    fn finish(self) -> Hash {
        self.0.finalize().into()
    }
}

fn plain_sha256(bytes: &[u8]) -> Hash {
    Sha256::digest(bytes).into()
}

fn get_cached(cache: &[Option<Hash>], index: usize) -> Option<Hash> {
    cache.get(index).copied().flatten()
}

fn set_cached(cache: &mut Vec<Option<Hash>>, index: usize, digest: Hash) {
    if index >= cache.len() {
        cache.resize(index + 1, None);
    }
    cache[index] = Some(digest);
}

fn hex(bytes: &Hash) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(64);
    for &byte in bytes {
        output.push(char::from(DIGITS[usize::from(byte >> 4)]));
        output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quotient_identity_is_sensitive_to_kind_type_and_dependencies() {
        let mut kernel = Kernel::new();
        let root = kernel.anon();
        let name = kernel.name_str(root, "Quot.synthetic");
        let parameter = kernel.name_str(root, "u");
        let dependency_a = kernel.name_str(root, "DependencyA");
        let dependency_b = kernel.name_str(root, "DependencyB");
        let ty = kernel.sort_zero();
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let alternate_type = kernel.sort(one);
        let dependency_type_a = kernel.const_(dependency_a, vec![]);
        let dependency_type_b = kernel.const_(dependency_b, vec![]);

        let make_declaration = |ty, kind| Declaration::Quotient {
            name,
            uparams: vec![parameter],
            ty,
            kind,
        };
        let declaration = make_declaration(ty, QuotKind::Type);
        let different_kind = make_declaration(ty, QuotKind::Ctor);
        let different_type = make_declaration(alternate_type, QuotKind::Type);
        let source_dependency = make_declaration(dependency_type_a, QuotKind::Type);
        let replacement_dependency = make_declaration(dependency_type_b, QuotKind::Type);

        let mut builder = IdentityBuilder::new(&kernel);
        let original_digest = builder
            .declaration_digest(&declaration)
            .expect("synthetic quotient identity");
        assert_ne!(
            original_digest,
            builder
                .declaration_digest(&different_kind)
                .expect("kind-mutated quotient identity")
        );
        assert_ne!(
            original_digest,
            builder
                .declaration_digest(&different_type)
                .expect("type-mutated quotient identity")
        );
        assert_ne!(
            builder
                .declaration_digest(&source_dependency)
                .expect("first dependency quotient identity"),
            builder
                .declaration_digest(&replacement_dependency)
                .expect("second dependency quotient identity")
        );
        assert_eq!(
            builder.direct_dependencies(&source_dependency),
            [dependency_a]
        );
        assert_eq!(
            builder.direct_dependencies(&replacement_dependency),
            [dependency_b]
        );
    }
}
