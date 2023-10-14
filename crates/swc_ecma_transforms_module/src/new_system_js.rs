use std::{iter, mem};

use serde::{Deserialize, Serialize};
use swc_atoms::JsWord;
use swc_common::{
    collections::{AHashMap, AHashSet},
    util::take::Take,
    Mark, Span, DUMMY_SP,
};
use swc_ecma_ast::*;
use swc_ecma_utils::{
    contains_top_level_await, find_pat_ids, function, ident::IdentLike, is_valid_prop_ident,
    member_expr, private_ident, quote_ident, quote_str, undefined, ExprFactory, IdentExt,
    IsDirective,
};
use swc_ecma_visit::{
    as_folder, noop_visit_mut_type, noop_visit_type, Fold, Visit, VisitMut, VisitMutWith, VisitWith,
};

use crate::{
    module_decl_strip::{Export, Link, LinkItem, LinkSpecifier, ModuleDeclStrip},
    top_level_this::top_level_this,
    util::{define_es_module, prop_name, use_strict, IdentOrStr, VecStmtLike},
};

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct Config {
    #[serde(default)]
    pub allow_top_level_this: bool,
}

struct SystemJs {
    config: Config,

    unresolved_mark: Mark,
    unresolved_span: Span,

    export_ident: Ident,
    context_ident: Ident,
    exports: Ident,

    export_map: LocalExport,
}

pub fn system_js(unresolved_mark: Mark, config: Config) -> impl Fold + VisitMut {
    as_folder(SystemJs {
        config,
        unresolved_mark,
        unresolved_span: DUMMY_SP.apply_mark(unresolved_mark),

        export_ident: private_ident!("_export"),
        context_ident: private_ident!("_context"),
        exports: private_ident!("exports"),

        export_map: Default::default(),
    })
}

impl VisitMut for SystemJs {
    noop_visit_mut_type!();

    fn visit_mut_script(&mut self, _: &mut Script) {
        // skip
    }

    fn visit_mut_module(&mut self, n: &mut Module) {
        let module_items = &mut n.body;

        let mut stmts: Vec<Stmt> = vec![];

        // Collect directives
        stmts.extend(
            module_items
                .iter_mut()
                .take_while(|i| i.directive_continue())
                .map(|i| i.take())
                .map(ModuleItem::expect_stmt),
        );

        // "use strict";
        if !stmts.has_use_strict() {
            stmts.push(use_strict());
        }

        let is_async = contains_top_level_await(module_items);

        if !self.config.allow_top_level_this {
            top_level_this(module_items, *undefined(DUMMY_SP));
        }

        let mut strip = ModuleDeclStrip::new(VarDeclKind::Var);
        module_items.visit_mut_with(&mut strip);

        let ModuleDeclStrip {
            link,
            export,
            export_assign,
            ..
        } = strip;

        let ImportData {
            mut var_list,
            dep_list,
            setters,
        } = self.handle_links(link);

        if !var_list.is_empty() {
            var_list.sort();
            stmts.push(
                VarDecl {
                    span: DUMMY_SP,
                    kind: VarDeclKind::Var,
                    declare: false,
                    decls: var_list
                        .into_iter()
                        .map(BindingIdent::from)
                        .map(Pat::Ident)
                        .map(|name| VarDeclarator {
                            span: DUMMY_SP,
                            name,
                            init: None,
                            definite: false,
                        })
                        .collect(),
                }
                .into(),
            );
        }

        stmts.push(self.build_exports(&export));
        stmts.push(define_es_module(self.exports.clone()));

        if export_assign.is_none() {
            // _export(exports);
            stmts.push(
                self.export_ident
                    .clone()
                    .as_call(DUMMY_SP, vec![self.exports.clone().as_arg()])
                    .into_stmt(),
            );
        }

        self.cacl_export_map(export);

        module_items.visit_mut_with(self);

        let mut execute_stmts: Vec<Stmt> = module_items
            .take()
            .into_iter()
            .filter_map(|i| match i {
                ModuleItem::Stmt(stmt) if !stmt.is_empty() => Some(stmt),
                _ => None,
            })
            .collect();

        if let Some(export_assign) = export_assign {
            let return_stmt = ReturnStmt {
                span: DUMMY_SP,
                arg: Some(export_assign),
            };

            execute_stmts.push(return_stmt.into())
        }

        // return {
        //     setters: [...],
        //     execute: function() {
        //     ...
        //     }
        // }
        let execute_fn = Function {
            params: vec![],
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: execute_stmts,
            }),
            is_generator: false,
            is_async,
            type_params: None,
            return_type: None,
        };

        let mut props = vec![];
        if setters.elems.iter().any(Option::is_some) {
            props.push(
                Prop::KeyValue(KeyValueProp {
                    key: PropName::Ident(quote_ident!("setters")),
                    value: setters.into(),
                })
                .into(),
            );
        }

        props.push(
            Prop::KeyValue(KeyValueProp {
                key: PropName::Ident(quote_ident!("execute")),
                value: execute_fn.into(),
            })
            .into(),
        );

        stmts.push(
            ReturnStmt {
                span: DUMMY_SP,
                arg: Some(
                    ObjectLit {
                        span: DUMMY_SP,
                        props,
                    }
                    .into(),
                ),
            }
            .into(),
        );

        let dep_list = ArrayLit {
            span: DUMMY_SP,
            elems: dep_list
                .into_iter()
                .map(Into::into)
                .map(|expr| ExprOrSpread { spread: None, expr })
                .map(Option::Some)
                .collect(),
        };

        let params = vec![
            self.export_ident.clone().into(),
            self.context_ident.clone().into(),
        ];

        let system_register_call = member_expr!(self.unresolved_span, System.register)
            .as_call(
                DUMMY_SP,
                vec![
                    dep_list.as_arg(),
                    Function {
                        params,
                        decorators: vec![],
                        span: DUMMY_SP,
                        body: Some(BlockStmt {
                            span: DUMMY_SP,
                            stmts,
                        }),
                        is_generator: false,
                        is_async: false,
                        type_params: None,
                        return_type: None,
                    }
                    .as_arg(),
                ],
            )
            .into_stmt();

        *module_items = vec![system_register_call.into()];
    }

    fn visit_mut_expr(&mut self, n: &mut Expr) {
        n.visit_mut_children_with(self);

        match n {
            Expr::Ident(ident)
                if ident.sym == "__moduleName"
                    && ident.span.ctxt.outer() == self.unresolved_mark =>
            {
                *n = self.context_ident.clone().make_member(quote_ident!("id"));
            }
            Expr::MetaProp(MetaPropExpr {
                span,
                kind: MetaPropKind::ImportMeta,
            }) => {
                *n = self.context_ident.clone().make_member(quote_ident!("meta"));
            }
            Expr::Assign(AssignExpr { left, .. }) => {
                let ids: Vec<Id> = find_pat_ids(left);
                if let Some(expr) = self.export(&ids) {
                    // [assign_expr, _export(..)][0]
                    *n = ArrayLit {
                        span: DUMMY_SP,
                        elems: vec![Some(n.take().into()), Some(expr.into())],
                    }
                    .computed_member::<Expr>(0.into());
                }
            }
            Expr::Update(UpdateExpr { prefix, arg, .. }) => {}
            _ => (),
        }
    }

    fn visit_mut_module_items(&mut self, n: &mut Vec<ModuleItem>) {
        n.visit_mut_children_with(self);

        let mut hoist_fn_list = vec![];
        for mut item in mem::replace(n, vec![ModuleItem::dummy()]) {
            match &mut item {
                ModuleItem::Stmt(Stmt::Decl(Decl::Fn(FnDecl { ident, .. }))) => {
                    hoist_fn_list.push(ident.to_id());
                }
                ModuleItem::Stmt(Stmt::Decl(Decl::Var(var))) => {
                    // TODO: is there any efficient way to filter out the elements without using
                    // clone?
                    let decls: Vec<VarDeclarator> = var
                        .decls
                        .iter()
                        .filter(|v| v.init.is_some())
                        .map(|v| VarDeclarator {
                            span: DUMMY_SP,
                            name: v.name.clone(),
                            init: None,
                            definite: false,
                        })
                        .collect();

                    let ids: Vec<Id> = find_pat_ids(&decls);
                    let mut list = self.get_export_list(&ids);

                    match list.len() {
                        0 => {}
                        1 if var.decls.len() == 1 && var.decls[0].name.is_ident() => {
                            // var x = _export("name", value)
                            let (export_name, export_value) = list.remove(0);
                            let init = *var.decls[0].init.take().unwrap();
                            var.decls[0].init = Some(self.export_one(export_name, init).into());
                        }
                        1 => {
                            // var { x } = {}; _export("x", x);
                            let (name, value) = list.remove(0);

                            let item = mem::replace(
                                &mut item,
                                self.export_one(name, value).into_stmt().into(),
                            );
                            n.push(item);
                        }
                        _ => {
                            // var x, y = value, [z] = []; _export({ y: y, z: z });
                            let item =
                                mem::replace(&mut item, self.export_batch(list).into_stmt().into());
                            n.push(item);
                        }
                    }
                }
                ModuleItem::Stmt(Stmt::Decl(Decl::Class(ClassDecl { ident, .. }))) => {
                    if let Some(expr) = self.export(&[ident.to_id()]) {
                        let item = mem::replace(&mut item, expr.into_stmt().into());
                        n.push(item);
                    }
                }
                _ => {}
            }
            n.push(item);
        }

        if !hoist_fn_list.is_empty() {
            if let Some(expr) = self.export(&hoist_fn_list) {
                n[0] = expr.into_stmt().into();
            }
        }
    }
}

impl SystemJs {
    fn handle_links(&self, link: Link) -> ImportData {
        let mut var_list = vec![];
        let mut dep_list = Vec::<JsWord>::with_capacity(link.capacity());
        let mut setters = ArrayLit {
            span: DUMMY_SP,
            elems: Vec::<_>::with_capacity(link.capacity()),
        };

        link.into_iter().for_each(
            |(src, LinkItem(src_span, link_specifier_set, mut link_flag))| {
                let mod_ident = private_ident!("_mod");

                dep_list.push(src);

                let mut setter_stmts = vec![];

                link_specifier_set.into_iter().for_each(|s| match s {
                    LinkSpecifier::Empty => {}
                    LinkSpecifier::ImportNamed { imported, local } => {
                        var_list.push(local.clone());

                        let key = imported.unwrap_or_else(|| local.0.clone());

                        let init = MemberExpr {
                            span: DUMMY_SP,
                            obj: mod_ident.clone().into(),
                            prop: prop_name(&key, DUMMY_SP).into(),
                        };

                        let stmt = init
                            .make_assign_to(op!("="), PatOrExpr::Pat(local.into()))
                            .into_stmt();
                        setter_stmts.push(stmt);
                    }
                    LinkSpecifier::ImportDefault(local) => {
                        var_list.push(local.clone());

                        let init = mod_ident.clone().make_member(quote_ident!("default"));
                        let stmt = init
                            .make_assign_to(op!("="), PatOrExpr::Pat(local.into()))
                            .into_stmt();
                        setter_stmts.push(stmt);
                    }
                    LinkSpecifier::ImportStarAs(local) => {
                        var_list.push(local.clone());

                        let init = mod_ident.clone();
                        let stmt = init
                            .make_assign_to(op!("="), PatOrExpr::Pat(local.into()))
                            .into_stmt();
                        setter_stmts.push(stmt);
                    }
                    LinkSpecifier::ExportNamed { orig, exported } => {
                        let export_name = exported.unwrap_or_else(|| orig.clone()).into();

                        let init = MemberExpr {
                            span: DUMMY_SP,
                            obj: mod_ident.clone().into(),
                            prop: prop_name(&orig.0, orig.1).into(),
                        };

                        setter_stmts.push(self.export_one(export_name, init.into()).into_stmt());
                    }
                    LinkSpecifier::ExportDefaultAs(default_span, local_sym, local_span) => {
                        let init = MemberExpr {
                            span: DUMMY_SP,
                            obj: mod_ident.clone().into(),
                            prop: prop_name(&local_sym, local_span).into(),
                        };

                        setter_stmts.push(
                            self.export_one(
                                IdentOrStr::new("default".into(), default_span),
                                init.into(),
                            )
                            .into_stmt(),
                        );
                    }
                    LinkSpecifier::ExportStarAs(export_name, export_span) => {
                        setter_stmts.push(
                            self.export_one(export_name.into(), mod_ident.clone().into())
                                .into_stmt(),
                        );
                    }
                    LinkSpecifier::ExportStar => {}
                    LinkSpecifier::ImportEqual(id) => {
                        var_list.push(id.clone());

                        let stmt = mod_ident
                            .clone()
                            .make_assign_to(op!("="), PatOrExpr::Pat(id.into()))
                            .into_stmt();
                        setter_stmts.push(stmt);
                    }
                });

                let setter = if setter_stmts.is_empty() {
                    None
                } else {
                    Some(
                        Function {
                            params: vec![mod_ident.into()],
                            decorators: vec![],
                            span: DUMMY_SP,
                            body: Some(BlockStmt {
                                span: DUMMY_SP,
                                stmts: setter_stmts,
                            }),
                            is_generator: false,
                            is_async: false,
                            type_params: None,
                            return_type: None,
                        }
                        .as_arg(),
                    )
                };

                setters.elems.push(setter);
            },
        );

        ImportData {
            var_list,
            dep_list,
            setters,
        }
    }

    /// ```JavaScript
    /// var exports = {
    ///   __proto__ = null;
    ///   fn: fn,
    ///   a: void 0
    /// };
    /// ```
    fn build_exports(&self, export: &Export) -> Stmt {
        let mut export_list: Vec<IdentOrStr> = export.iter().map(Into::into).collect();
        export_list.sort();

        let props = export_list.into_iter().map(|export_name| KeyValueProp {
            key: if export_name.is_specific_name("__proto__") {
                PropName::Computed(ComputedPropName {
                    span: DUMMY_SP,
                    expr: export_name.into_str().into(),
                })
            } else {
                export_name.into()
            },
            value: undefined(DUMMY_SP),
        });

        let props = iter::once(KeyValueProp {
            key: quote_ident!("__proto__").into(),
            value: Null { span: DUMMY_SP }.into(),
        })
        .chain(props)
        .map(Prop::KeyValue)
        .map(Box::new)
        .map(PropOrSpread::Prop)
        .collect();

        ObjectLit {
            span: DUMMY_SP,
            props,
        }
        .into_var_decl(VarDeclKind::Var, Pat::Ident(self.exports.clone().into()))
        .into()
    }

    fn cacl_export_map(&mut self, export: Export) {
        for (export_name, export_item) in export {
            let export_name = IdentOrStr::new(export_name, export_item.export_name_span());
            let id = export_item.into_local_ident().to_id();

            self.export_map.entry(id).or_default().insert(export_name);
        }
    }

    // _export("name", value)
    fn export_one(&self, export_name: IdentOrStr, value: Expr) -> Expr {
        self.export_ident.clone().as_call(
            DUMMY_SP,
            vec![export_name.into_str().as_arg(), value.as_arg()],
        )
    }

    // _export({ a: value, b: value })
    fn export_batch(&self, mut list: Vec<(IdentOrStr, Expr)>) -> Expr {
        list.sort_by(|(a, _), (b, _)| a.cmp(b));

        let props = list
            .into_iter()
            .map(|(key, value)| KeyValueProp {
                key: key.into(),
                value: value.into(),
            })
            .map(Prop::KeyValue)
            .map(Into::into)
            .collect();

        self.export_ident.clone().as_call(
            DUMMY_SP,
            vec![ObjectLit {
                span: DUMMY_SP,
                props,
            }
            .as_arg()],
        )
    }

    fn get_export_list(&self, ids: &[Id]) -> Vec<(IdentOrStr, Expr)> {
        ids.iter()
            .filter_map(|key| self.export_map.get_key_value(key))
            .flat_map(|(key, set)| iter::repeat(key).zip(set))
            .map(|(local, export_name)| (export_name.clone(), local.clone().into()))
            .collect()
    }

    fn export(&self, ids: &[Id]) -> Option<Expr> {
        let mut list = self.get_export_list(ids);

        match list.len() {
            0 => None,
            1 => {
                let (name, value) = list.remove(0);
                Some(self.export_one(name, value))
            }
            _ => Some(self.export_batch(list)),
        }
    }
}

type LocalExport = AHashMap<Id, AHashSet<IdentOrStr>>;

struct ImportData {
    var_list: Vec<Id>,
    dep_list: Vec<JsWord>,
    setters: ArrayLit,
}
