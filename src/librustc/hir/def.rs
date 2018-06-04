// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use hir::def_id::DefId;
use util::nodemap::{NodeMap, DefIdMap};
use syntax::ast;
use syntax::ext::base::MacroKind;
use syntax_pos::Span;
use hir;
use ty;

use std::iter::{once, Once, Chain};

use self::Namespace::*;

#[derive(Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug)]
pub enum CtorKind {
    /// Constructor function automatically created by a tuple struct/variant.
    Fn,
    /// Constructor constant automatically created by a unit struct/variant.
    Const,
    /// Unusable name in value namespace created by a struct variant.
    Fictive,
}

#[derive(Clone, Copy, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug)]
pub enum Def {
    // Type namespace
    Mod(DefId),
    Struct(DefId), // DefId refers to NodeId of the struct itself
    Union(DefId),
    Enum(DefId),
    Variant(DefId),
    Trait(DefId),
    TyAlias(DefId),
    TyForeign(DefId),
    TraitAlias(DefId),
    AssociatedTy(DefId),
    PrimTy(hir::PrimTy),
    TyParam(DefId),
    SelfTy(Option<DefId> /* trait */, Option<DefId> /* impl */),

    // Value namespace
    Fn(DefId),
    Const(DefId),
    Static(DefId, bool /* is_mutbl */),
    StructCtor(DefId, CtorKind), // DefId refers to NodeId of the struct's constructor
    VariantCtor(DefId, CtorKind),
    Method(DefId),
    AssociatedConst(DefId),

    Local(ast::NodeId),
    Upvar(ast::NodeId,  // node id of closed over local
          usize,        // index in the freevars list of the closure
          ast::NodeId), // expr node that creates the closure
    Label(ast::NodeId),

    // Macro namespace
    Macro(DefId, MacroKind),

    GlobalAsm(DefId),

    // Both namespaces
    Err,
}

impl Default for Def {
    fn default() -> Self {
        Def::Err
    }
}

/// The result of resolving a path before lowering to HIR.
/// `base_def` is definition of resolved part of the
/// path, `unresolved_segments` is the number of unresolved
/// segments.
///
/// ```text
/// module::Type::AssocX::AssocY::MethodOrAssocType
/// ^~~~~~~~~~~~  ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// base_def      unresolved_segments = 3
///
/// <T as Trait>::AssocX::AssocY::MethodOrAssocType
///       ^~~~~~~~~~~~~~  ^~~~~~~~~~~~~~~~~~~~~~~~~
///       base_def        unresolved_segments = 2
/// ```
#[derive(Copy, Clone, Debug)]
pub struct PathResolution {
    base_def: Def,
    unresolved_segments: usize,
}

impl PathResolution {
    pub fn new(def: Def) -> Self {
        PathResolution { base_def: def, unresolved_segments: 0 }
    }

    pub fn with_unresolved_segments(def: Def, mut unresolved_segments: usize) -> Self {
        if def == Def::Err { unresolved_segments = 0 }
        PathResolution { base_def: def, unresolved_segments: unresolved_segments }
    }

    #[inline]
    pub fn base_def(&self) -> Def {
        self.base_def
    }

    #[inline]
    pub fn unresolved_segments(&self) -> usize {
        self.unresolved_segments
    }

    pub fn kind_name(&self) -> &'static str {
        if self.unresolved_segments != 0 {
            "associated item"
        } else {
            self.base_def.kind_name()
        }
    }
}

/// Different kinds of symbols don't influence each other.
///
/// Therefore, they have a separate universe (namespace).
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Namespace {
    TypeNS,
    ValueNS,
    MacroNS,
}

/// Just a helper ‒ separate structure for each namespace.
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Hash, RustcEncodable, RustcDecodable)]
pub struct PerNS<T> {
    pub value_ns: T,
    pub type_ns: T,
    pub macro_ns: T,
}

impl<T> PerNS<T> {
    /// Applies the given function to every item in the collection, returning the result.
    pub fn map<U, F: FnMut(T) -> U>(self, mut f: F) -> PerNS<U> {
        PerNS {
            value_ns: f(self.value_ns),
            type_ns: f(self.type_ns),
            macro_ns: f(self.macro_ns),
        }
    }
}

impl<T> PerNS<Option<T>> {
    /// Returns whether there are no items in any namespace.
    pub fn is_empty(&self) -> bool {
        self.value_ns.is_none() && self.type_ns.is_none() && self.macro_ns.is_none()
    }
}

impl PerNS<Def> {
    /// Ensures that no more than one namespace has a valid `Def`, then returns that `Def` (or
    /// `Err` if no namespaces had valid `Def`s).
    pub fn assert_single_ns(self) -> Def {
        let mut valid_defs = self.into_iter().filter(|d| *d != Def::Err).collect::<Vec<Def>>();
        if valid_defs.len() > 1 {
            bug!("single Def was requested but multiple were available: {:?}", valid_defs);
        }
        valid_defs.pop().unwrap_or(Def::Err)
    }

    /// Returns whether all the `Def`s in this collection are `Err`.
    pub fn all_err(self) -> bool {
        self.into_iter().all(|d| d == Def::Err)
    }

    /// Returns an iterator over the valid `Def`s in this collection. If all the `Def`s are `Err`,
    /// the iterator will yield a single `Err`.
    pub fn valid_defs(self) -> impl Iterator<Item=Def> {
        if self.all_err() {
            vec![Def::Err].into_iter()
        } else {
            let mut ret = Vec::with_capacity(3);
            ret.extend(self.into_iter().filter(|&d| d != Def::Err));
            ret.into_iter()
        }
    }
}

impl<T> ::std::ops::Index<Namespace> for PerNS<T> {
    type Output = T;
    fn index(&self, ns: Namespace) -> &T {
        match ns {
            ValueNS => &self.value_ns,
            TypeNS => &self.type_ns,
            MacroNS => &self.macro_ns,
        }
    }
}

impl<T> ::std::ops::IndexMut<Namespace> for PerNS<T> {
    fn index_mut(&mut self, ns: Namespace) -> &mut T {
        match ns {
            ValueNS => &mut self.value_ns,
            TypeNS => &mut self.type_ns,
            MacroNS => &mut self.macro_ns,
        }
    }
}

/// Iterates over the namespaces: first the Type, then the Value, then the Macro.
impl<T> IntoIterator for PerNS<T> {
    type Item = T;
    type IntoIter = Chain<Chain<Once<T>, Once<T>>, Once<T>>;

    fn into_iter(self) -> Self::IntoIter {
        once(self.type_ns).chain(once(self.value_ns)).chain(once(self.macro_ns))
    }
}

impl From<Def> for PerNS<Def> {
    fn from(src: Def) -> PerNS<Def> {
        let mut ret = PerNS::<Def>::default();

        if let Some(ns) = src.namespace() {
            ret[ns] = src;
        }

        ret
    }
}

/// Definition mapping
pub type DefMap = NodeMap<PerNS<Option<PathResolution>>>;

/// This is the replacement export map. It maps a module to all of the exports
/// within.
pub type ExportMap = DefIdMap<Vec<Export>>;

#[derive(Copy, Clone, Debug, RustcEncodable, RustcDecodable)]
pub struct Export {
    /// The name of the target.
    pub ident: ast::Ident,
    /// The definition of the target.
    pub def: Def,
    /// The span of the target definition.
    pub span: Span,
    /// The visibility of the export.
    /// We include non-`pub` exports for hygienic macros that get used from extern crates.
    pub vis: ty::Visibility,
}

impl CtorKind {
    pub fn from_ast(vdata: &ast::VariantData) -> CtorKind {
        match *vdata {
            ast::VariantData::Tuple(..) => CtorKind::Fn,
            ast::VariantData::Unit(..) => CtorKind::Const,
            ast::VariantData::Struct(..) => CtorKind::Fictive,
        }
    }
    pub fn from_hir(vdata: &hir::VariantData) -> CtorKind {
        match *vdata {
            hir::VariantData::Tuple(..) => CtorKind::Fn,
            hir::VariantData::Unit(..) => CtorKind::Const,
            hir::VariantData::Struct(..) => CtorKind::Fictive,
        }
    }
}

impl Def {
    pub fn def_id(&self) -> DefId {
        match *self {
            Def::Fn(id) | Def::Mod(id) | Def::Static(id, _) |
            Def::Variant(id) | Def::VariantCtor(id, ..) | Def::Enum(id) |
            Def::TyAlias(id) | Def::TraitAlias(id) |
            Def::AssociatedTy(id) | Def::TyParam(id) | Def::Struct(id) | Def::StructCtor(id, ..) |
            Def::Union(id) | Def::Trait(id) | Def::Method(id) | Def::Const(id) |
            Def::AssociatedConst(id) | Def::Macro(id, ..) |
            Def::GlobalAsm(id) | Def::TyForeign(id) => {
                id
            }

            Def::Local(..) |
            Def::Upvar(..) |
            Def::Label(..)  |
            Def::PrimTy(..) |
            Def::SelfTy(..) |
            Def::Err => {
                bug!("attempted .def_id() on invalid def: {:?}", self)
            }
        }
    }

    /// A human readable kind name
    pub fn kind_name(&self) -> &'static str {
        match *self {
            Def::Fn(..) => "function",
            Def::Mod(..) => "module",
            Def::Static(..) => "static",
            Def::Variant(..) => "variant",
            Def::VariantCtor(.., CtorKind::Fn) => "tuple variant",
            Def::VariantCtor(.., CtorKind::Const) => "unit variant",
            Def::VariantCtor(.., CtorKind::Fictive) => "struct variant",
            Def::Enum(..) => "enum",
            Def::TyAlias(..) => "type alias",
            Def::TraitAlias(..) => "trait alias",
            Def::AssociatedTy(..) => "associated type",
            Def::Struct(..) => "struct",
            Def::StructCtor(.., CtorKind::Fn) => "tuple struct",
            Def::StructCtor(.., CtorKind::Const) => "unit struct",
            Def::StructCtor(.., CtorKind::Fictive) => bug!("impossible struct constructor"),
            Def::Union(..) => "union",
            Def::Trait(..) => "trait",
            Def::TyForeign(..) => "foreign type",
            Def::Method(..) => "method",
            Def::Const(..) => "constant",
            Def::AssociatedConst(..) => "associated constant",
            Def::TyParam(..) => "type parameter",
            Def::PrimTy(..) => "builtin type",
            Def::Local(..) => "local variable",
            Def::Upvar(..) => "closure capture",
            Def::Label(..) => "label",
            Def::SelfTy(..) => "self type",
            Def::Macro(.., macro_kind) => macro_kind.descr(),
            Def::GlobalAsm(..) => "global asm",
            Def::Err => "unresolved item",
        }
    }

    /// The namespace associated with this Def. Returns `None` for `Err`.
    pub fn namespace(&self) -> Option<Namespace> {
        match *self {
            Def::Mod(..) |
            Def::Struct(..) |
            Def::Union(..) |
            Def::Enum(..) |
            Def::Variant(..) |
            Def::Trait(..) |
            Def::TyAlias(..) |
            Def::TyForeign(..) |
            Def::TraitAlias(..) |
            Def::AssociatedTy(..) |
            Def::PrimTy(..) |
            Def::TyParam(..) |
            Def::SelfTy(..) => Some(TypeNS),

            Def::Fn(..) |
            Def::Const(..) |
            Def::Static(..) |
            Def::StructCtor(..) |
            Def::VariantCtor(..) |
            Def::Method(..) |
            Def::AssociatedConst(..) |
            Def::Local(..) |
            Def::Upvar(..) |
            Def::Label(..) => Some(ValueNS),

            Def::Macro(..) |
            Def::GlobalAsm(..) => Some(MacroNS),

            Def::Err => None,
        }
    }
}
