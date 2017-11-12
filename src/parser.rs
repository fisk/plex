use std::collections::{BTreeMap, BTreeSet};
use std::{cmp, fmt};
use std::fmt::Write;

use lalr::*;

use syn;
use syn::buffer::Cursor;
use syn::synom::{PResult, Synom};
use syn::{Expr, Ident, Lifetime, LitStr, Meta, Type, Visibility};
use quote::Tokens;
use proc_macro2::{Delimiter, Span};
use proc_macro;
use proc_macro::TokenStream;

/// A pattern used as a terminal. This is supposed to be an enum variant.
#[derive(PartialEq, Eq, Copy, Clone, PartialOrd, Ord)]
struct TerminalPattern {
    // N.B. this compares unhygienically, which is what we want.
    ident: Ident,
    /// Whether the terminal was written as a unit-like variant `Terminal`,
    /// as opposed to a tuple-like variant `Terminal(a1, a2)`.
    unit_like: bool,
}

impl fmt::Debug for TerminalPattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.ident.fmt(f)
    }
}

impl fmt::Display for TerminalPattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.ident.fmt(f)
    }
}

/// Return the most frequent item in the given iterator, or None if it is empty.
/// Picks an arbitrary item in case of a tie.
fn most_frequent<T: Ord, I: Iterator<Item = T>>(it: I) -> Option<T> {
    let mut freq = BTreeMap::new();
    for x in it {
        *freq.entry(x).or_insert(0) += 1;
    }
    freq.into_iter().max_by_key(|&(_, f)| f).map(|(x, _)| x)
}

fn expected_one_of<S: fmt::Display>(xs: &[S]) -> String {
    let mut err_msg: String = "expected".to_string();
    for (i, x) in xs.iter().enumerate() {
        if i == 0 {
            let _ = write!(&mut err_msg, " ");
        } else if i == xs.len() - 1 {
            if i == 1 {
                let _ = write!(&mut err_msg, " or ");
            } else {
                let _ = write!(&mut err_msg, ", or ");
            }
        } else {
            let _ = write!(&mut err_msg, ", ");
        }
        let _ = write!(&mut err_msg, "{}", x);
    }
    err_msg
}

pub fn lr1_machine<'a, T, N, A, FM, FA, FR, FO>(
    grammar: &'a Grammar<T, N, A>,
    types: &BTreeMap<N, Tokens>,
    token_ty: Tokens,
    span_ty: Tokens,
    range_fn_id: Ident,
    range_fn: Tokens,
    name: Ident,
    mut to_pat: FM,
    mut to_expr: FA,
    reduce_on: FR,
    priority_of: FO,
) -> Result<Tokens, LR1Conflict<'a, T, N, A>>
where
    T: Ord + fmt::Debug + fmt::Display,
    N: Ord + fmt::Debug,
    A: fmt::Debug,
    FM: FnMut(&T) -> Tokens,
    FA: FnMut(&N, &A, &[Symbol<T, N>]) -> (Tokens, Vec<Option<Tokens>>, Span),
    FR: FnMut(&Rhs<T, N, A>, Option<&T>) -> bool,
    FO: FnMut(&Rhs<T, N, A>, Option<&T>) -> i32,
{
    let actual_start = match grammar
        .rules
        .get(&grammar.start)
        .expect("Grammar didn't contain its start nonterminal")[0]
        .syms[0]
    {
        Terminal(_) => panic!("bad grammar"),
        Nonterminal(ref x) => x,
    };
    let table: LR1ParseTable<T, N, A> = grammar.lalr1(reduce_on, priority_of)?;
    let rule_fn_ids: BTreeMap<_, _> = grammar
        .rules
        .iter()
        .filter(|&(lhs, _)| *lhs != grammar.start)
        .flat_map(|(_, rhss)| {
            // Identify rules by their RHS, which should have unique addresses
            rhss.iter().map(|rhs| rhs as *const _)
        })
        .enumerate()
        .map(|(i, k)| (k, Ident::new(format!("reduce_{}", i), Span::def_site())))
        .collect();
    let goto_fn_ids: BTreeMap<_, _> = grammar
        .rules
        .keys()
        .filter(|&lhs| *lhs != grammar.start)
        .enumerate()
        .map(|(i, lhs)| (lhs, Ident::new(format!("goto_{}", i), Span::def_site())))
        .collect();

    let mut stmts = Vec::new();

    stmts.push(range_fn);
    stmts.push(
        quote!(fn range_array(x: &[Option<#span_ty>]) -> Option<#span_ty> {
        if let Some(lo) = x.iter().filter_map(|&x| x).next() {
            let hi = x.iter().rev().filter_map(|&x| x).next().unwrap();
            Some(#range_fn_id(lo, hi))
        } else {
            None
        }
    }),
    );
    for (lhs, rhss) in &grammar.rules {
        if *lhs == grammar.start {
            continue;
        }
        let goto_fn = goto_fn_ids[lhs];
        let lhs_ty = &types[lhs];
        for rhs in rhss.iter() {
            let (result, arg_pats, span) = to_expr(lhs, &rhs.act, cx, &rhs.syms);
            let len = rhs.syms.len();
            let current_span_stmt = if rhs.syms.len() > 0 {
                quote!(
                    let current_span: Option<#span_ty> = {
                        let sp = range_array(&span_stack[(span_stack.len() - #len)..]);
                        // XXX: Annoying syntax :( NLL soon!
                        let x = span_stack.len() - #len;
                        span_stack.truncate(x);
                        // Make the current_span available to the user by exposing it through a macro, whose name is unhygienic.
                        #[allow(unused_macros)] macro_rules! span {
                            () => { current_span.unwrap() }
                        }
                    };
                )
            } else {
                quote!(
                    let current_span: Option<#span_ty> = None;
                )
            };
            let mut reduce_stmts = vec![current_span_stmt];
            reduce_stmts.extend(rhs.syms.iter().zip(arg_pats.iter().cloned()).rev().map(
                |(sym, maybe_pat)| match maybe_pat {
                    Some(pat) => {
                        let ty = match *sym {
                            Terminal(_) => token_ty.clone(),
                            Nonterminal(ref n) => types[n].clone(),
                        };
                        quote!(
                        let #pat: #ty = *stack.pop().unwrap().downcast().unwrap();
                    )
                    }
                    None => quote!(
                    stack.pop();
                ),
                },
            ));
            // Workaround; closures sometimes complain about capturing from externals
            // if we don't "let" themselves within the closure first
            let result = arg_pats
                .into_iter()
                .fold(result, |acc, maybe_pat| match maybe_pat {
                    Some(pat) => {
                        if let ast::PatKind::Ident(_, sid, _) = pat.node {
                            quote!({ let #pat = #sid; #acc })
                        } else {
                            acc
                        }
                    }
                    None => acc,
                });
            if rhs.syms.len() > 1 {
                let len_minus_one = rhs.syms.len() - 1;
                // XXX: Annoying syntax :(
                reduce_stmts.push(
                    quote!(match state_stack.len() - #len_minus_one { x => #state_stack.trucate(x) };),
                );
            } else if rhs.syms.len() == 0 {
                reduce_stmts.push(quote!(state_stack.push(*state);).unwrap());
            }
            reduce_stmts.push(quote!(*state = #goto_fn(*state_stack.last().unwrap());));
            let rspan = result.span;

            reduce_stmts.push(quote!(
                let result: #lhs_ty = ( || -> #lhs_ty { #result } )();
            ));
            reduce_stmts.push(quote!(
                stack.push(Box::new(result) as Box<::std::any::Any>);
            ));
            reduce_stmts.push(quote!(span_stack.push(current_span);));

            let fn_id = rule_fn_ids.get(&(rhs as *const _)).unwrap().clone();
            stmts.push(quote!(
                fn #fn_id(
                    stack: &mut Vec<Box<::std::any::Any>>,
                    span_stack: &mut Vec<Option<#span_ty>>,
                    state_stack: &mut Vec<u32>,
                    state: &mut u32,
                ) {
                    #(#reduce_stmts)*
                }
            ));
        }
    }
    for (lhs, id) in &goto_fn_ids {
        let expr = if let Some(&most_freq) =
            most_frequent(table.states.iter().filter_map(|state| state.goto.get(lhs)))
        {
            let most_freq = most_freq as u32;
            let mut pats_by_dest = BTreeMap::new();
            for (ix, state) in table.states.iter().enumerate() {
                if let Some(&dest) = state.goto.get(lhs) {
                    let dest = dest as u32;
                    if dest != most_freq {
                        pats_by_dest
                            .entry(dest)
                            .or_insert(vec![])
                            .push(pat_u32(cx, ix as u32));
                    }
                }
            }
            let mut arms: Vec<_> = pats_by_dest
                .into_iter()
                .map(|(dest, pats)| quote!(#(#pats)|* => #dest,))
                .collect();
            arms.push(quote!(_ => #most_freq,));
            quote!(match state { #(#arms)* })
        } else {
            // This shouldn't normally happen, but it can when `lhs` is unused in the
            // grammar.
            quote!(unreachable!())
        };
        stmts.push(quote!(fn #id(state: u32) -> u32 {
            expr
        }));
    }
    stmts.push(quote!(
        let stack = Vec::new();
        let span_stack = Vec::new();
        let state_stack = Vec::new();
        let state: u32 = 0;
        let token_span = it.next();
    ));
    stmts.push({
        let state_arms = table.states.iter().enumerate().map(|(ix, state)| {
            let mut arms = vec![];
            let mut reduce_arms = BTreeMap::new();
            let mut expected = vec![];
            for (&tok, action) in state.lookahead.iter() {
                expected.push(format!("`{}`", tok));
                let tok_pat = top_pat(tok);
                let pat = quote!(Some((#tok_pat, _)));
                let arm_expr = match *action {
                    LRAction::Shift(dest) => dest as u32,
                    LRAction::Reduce(_, rhs) => {
                        reduce_arms
                            .entry(rhs as *const _)
                            .or_insert(vec![])
                            .push(pat);
                        continue;
                    }
                    LRAction::Accept => unreachable!(),
                };
                arms.push(quote!(#pat => #arm_expr,));
            }
            if let Some(ref action) = state.eof {
                expected.push("end of file".to_string());
                let pat = quote!(None);
                match *action {
                    LRAction::Shift(_) => unreachable!(),
                    LRAction::Reduce(_, rhs) => {
                        reduce_arms
                            .entry(rhs as *const _)
                            .or_insert(vec![])
                            .push(pat);
                    }
                    LRAction::Accept => {
                        let ty = &types[actual_start];
                        let arm_expr = quote!(
                                return Ok(*stack.pop().unwrap().downcast::<#ty>().unwrap())
                            );
                        arms.push(quote!(#pat => #arm_expr,));
                    }
                };
            }
            for (rhs_ptr, pats) in reduce_arms.into_iter() {
                let reduce_fn = rule_fn_ids[&rhs_ptr];
                arms.push(quote!(#(#pats)|* => {
                        $reduce_fn(&mut $stack_id, &mut $span_stack_id, &mut $state_stack_id, &mut $state_id);
                        continue
                    }));
            }
            let err_msg = expected_one_of(&expected);
            arms.push(quote!(_ => return Err((token_span, #err_msg)),));
            let ix = ix as u32;
            quote!(#ix => match token_span { #(#arms)* })
        });
        quote!(
            loop {
                let next_state = match state {
                    #(#state_arms)*
                    _ => unreachable!(),
                };
                match token_span {
                    Some((token, span)) => {
                        stack.push(Box::new(token) as Box<::std::any::Any>);
                        span_stack.push(Some(span));
                    }
                    None => unreachable!(),
                };
                state_stack.push(state);
                token_span = it.next();
                state = next_state;
            }
        )
    });
    quote!(
        fn #name<I: Iterator<Item=(#token_ty, #span_ty)>>(mut it: I) -> Result<#start_type, (Option<(#token_ty, #span_ty)>, &'static str)> {
            #(#stmts)*
        }
    )
}

enum RuleLhsItem {
    Symbol(Ident),
    SymbolPat(Ident, Pat),
    Destructure(Ident, Vec<Pat>),
}

struct Rule {
    lhs: Vec<RuleLhsItem>,
    lhs_span: proc_macro::Span,
    rhs: Expr,
    exclusions: BTreeSet<Ident>,
    exclude_eof: bool,
    priority: i32,
}

fn parse_rules(mut input: Cursor) -> PResult<Vec<Rule>> {
    let mut rules = vec![];
    while !input.eof() {
        // FIXME: Make some nicer error messages, preferably when syn supports it.
        let mut exclusions = BTreeSet::empty();
        let mut exclude_eof = false;
        let mut priority = 0;
        let (metas, input_) = many0!(
            input,
            do_parse!(punct!(#) >> meta: brackets!(syn!(Meta)) >> meta.0)
        );
        input = input_;
        for meta in metas {
            match meta {
                Meta::List(ref list) if list.ident == "no_reduce" => {
                    for token in &list.nested {
                        if let NestedMeta::Meta(Meta::Word(ident)) = *token {
                            if ident == "EOF" {
                                exclude_eof = true;
                            } else {
                                exclusions.insert(ident);
                            }
                        } else {
                            // FIXME bad span here
                            list.paren_token
                                .span
                                .unstable()
                                .error("invalid syntax: no_reduce list includes a non-token")
                                .emit();
                        }
                    }
                }
                Meta::Word(ref ident) if ident == "overriding" => {
                    priority = 1;
                }
                _ => {
                    // FIXME non-ideal span
                    meta.name()
                        .span
                        .unstable()
                        .error("unknown attribute")
                        .emit();
                }
            }
        }
        let mut lhs = vec![];
        let sp_lo = input.span();
        let mut sp_hi = sp_lo;
        while let Some(ident, input_) = Ident::parse(input) {
            input = input_;
            lhs.push(
                if let Some((inner, span, input_)) = input.group(Delimiter::Bracket) {
                    sp_hi = span;
                    input = input_;
                    let (pat, inner_) = Pat::parse(inner)?;
                    input_end!(inner_)?;
                    RuleLhsItem::SymbolPat(ident, pat)
                } else if let Some((mut inner, span, input_)) = input.group(Delimiter::Brace) {
                    sp_hi = span;
                    input = input_;
                    let mut pats = vec![];
                    while !inner.eof() {
                        let (pat, inner_) = Pat::parse(inner)?;
                        pats.push(pat);
                        inner = inner_;
                        if !inner.eof() {
                            let (_, inner_) = <Token![,]>::parse(inner)?;
                            inner = inner_;
                        }
                    }
                    RuleLhsItem::Destructure(ident, pats)
                } else {
                    sp_hi = ident.span;
                    RuleLhsItem::Symbol(ident)
                },
            );
        }
        let lhs_span = sp_lo.unstable().join(sp_hi.unstable());
        let (_, input_) = <Token![=>]>::parse(input)?;
        input = input_;
        // Like in a `match` expression, braced block doesn't require a comma before the next rule.
        let optional_comma = input.group(Delimiter::Brace).is_some();
        let (rhs, input_) = Expr::parse(input)?;
        input = input_;
        rules.push(Rule {
            lhs,
            lhs_span,
            rhs,
            exclusions,
            exclude_eof,
            priority,
        });
        match <Token![,]>::parse(input) {
            Ok((_, input_)) => {
                input = input_;
            }
            Err(e) => {
                if !input.eof() && !optional_comma {
                    return Err(e);
                }
            }
        }
    }
    Ok((rules, input))
}

struct RuleSet {
    lhs: Ident,
    return_ty: Type,
    rules: Vec<Rule>,
}

impl Synom for RuleSet {
    named!(parse -> Self, do_parse!(
        lhs: syn!(Ident) >>
        punct!(:) >>
        return_ty: syn!(Type) >>
        rules: braces!(call!(parse_rules)) >>
        ({
            let (_, rules) = rules;
            RuleSet { lhs, return_ty, rules }
        })
    ));
}

struct Parser {
    vis: Visibility,
    name: Ident,
    token_ty: Type,
    span_ty: Type,
    range_fn: Option<(Ident, Ident, Block)>,
    rule_sets: Vec<RuleSet>,
}

impl Synom for Parser {
    named!(parse -> Self, do_parse!(
        vis: syn!(Visibility) >>
        keyword!(fn) >>
        name: syn!(Ident) >>
        token_and_span: parens!(tuple!(
            syn!(Type),
            punct!(,),
            syn!(Type),
        )) >>
        punct!(;) >>
        range_fn: option!(do_parse!(
            args: parens!(tuple!(syn!(Ident), punct!(,), syn!(Ident))) >>
            body: syn!(Block) >>
            ({
                let (_, (a, _, b)) = args;
                (a, b, body)
            })
        )) >>
        rule_sets: many0!(syn!(RuleSet)) >>
        ({
            let (_, (token_ty, _, span_ty)) = token_and_span;
            Parser { vis, name, token_ty, span_ty, range_fn, rule_sets }
        })
    ));
}

fn pretty_rule(lhs: Ident, syms: &[Symbol<TerminalPattern, Ident>]) -> String {
    let mut r = String::new();
    let _ = write!(&mut r, "{} ->", lhs);
    for sym in syms.iter() {
        let _ = write!(&mut r, " {}", sym);
    }
    r
}

// Pretty-print an item set, for error messages.
fn pretty(x: &ItemSet<TerminalPattern, Ident, Rule>, pad: &str) -> String {
    let mut r = String::new();
    let mut first = true;
    for item in x.items.iter() {
        if first {
            first = false;
        } else {
            let _ = write!(&mut r, "\n{}", pad);
        }
        let _ = write!(&mut r, "{} ->", item.lhs);
        for j in 0..item.pos {
            let _ = write!(&mut r, " {}", item.rhs.syms[j]);
        }
        let _ = write!(&mut r, " •");
        for j in item.pos..item.rhs.syms.len() {
            let _ = write!(&mut r, " {}", item.rhs.syms[j]);
        }
    }
    r
}

fn parser(input: TokenStream) -> TokenStream {
    let mut rules = BTreeMap::new();
    let mut types = BTreeMap::new();
    let mut start = None;
    while !parser.check(&token::Eof) {
        // parse "LHS: Type {"
        let lhs = try!(parser.parse_ident()).name;
        if start.is_none() {
            start = Some(lhs);
        }
        if rules.contains_key(&lhs) {
            let sp = parser.prev_span;
            parser.span_err(sp, "duplicate nonterminal");
        }
        try!(parser.expect(&token::Colon));
        let ty = try!(parser.parse_ty());
        types.insert(lhs, ty);
        try!(parser.expect(&token::OpenDelim(token::Brace)));
        let mut rhss = Vec::new();
        while !parser.check(&token::CloseDelim(token::Brace)) {
            let mut exclusions = BTreeSet::new();
            let mut priority = 0;
            while parser.check(&token::Pound) {
                // attributes
                let attr = try!(parser.parse_attribute(false)); // don't allow "#![..]" syntax
                match attr.meta() {
                    Some(ast::MetaItem {
                        name,
                        node: ast::MetaItemKind::List(ref tokens),
                        ..
                    }) if name == "no_reduce" =>
                    {
                        for token in tokens.iter() {
                            if let ast::NestedMetaItemKind::MetaItem(ref meta_item) = token.node {
                                if let ast::MetaItemKind::Word = meta_item.node {
                                    exclusions.insert(meta_item.name.to_string());
                                    continue;
                                }
                            }
                            parser.span_err(token.span, "not the name of a token");
                        }
                    }
                    Some(ast::MetaItem {
                        name,
                        node: ast::MetaItemKind::Word,
                        ..
                    }) if name == "overriding" =>
                    {
                        priority = 1;
                    }
                    _ => parser.span_err(attr.span, "unknown attribute"),
                }
            }
            let lo = parser.span.lo();
            let (mut rule, mut binds) = (vec![], vec![]);
            while !parser.check(&token::FatArrow) {
                let lo = parser.span.lo();
                let name = UnhygienicIdent(try!(parser.parse_ident()));
                let bind = if parser.eat(&token::OpenDelim(token::Bracket)) {
                    let r = try!(parser.parse_pat());
                    try!(parser.expect(&token::CloseDelim(token::Bracket)));
                    Binding::Pat(r)
                } else if parser.eat(&token::OpenDelim(token::Paren)) {
                    let mut pats = vec![];
                    while !parser.eat(&token::CloseDelim(token::Paren)) {
                        pats.push(try!(parser.parse_pat()));
                        if !parser.eat(&token::Comma) {
                            try!(parser.expect(&token::CloseDelim(token::Paren)));
                            break;
                        }
                    }
                    Binding::Enum(parser.prev_span.with_lo(lo), pats)
                } else {
                    Binding::None
                };
                rule.push(name);
                binds.push(bind);
            }
            let (rule, binds) = (rule, binds);

            try!(parser.expect(&token::FatArrow));

            // start parsing the expr
            let expr = try!(parser.parse_expr_res(parser::Restrictions::STMT_EXPR, None));
            let optional_comma =
                // don't need a comma for blocks...
                !classify::expr_requires_semi_to_be_stmt(&*expr)
                // or for the last arm
                || parser.check(&token::CloseDelim(token::Brace));

            if optional_comma {
                // consume optional comma
                parser.eat(&token::Comma);
            } else {
                // comma required
                try!(parser.expect_one_of(&[token::Comma], &[token::CloseDelim(token::Brace)]));
            }
            let sp = parser.prev_span.with_lo(lo);

            rhss.push((
                rule,
                Action {
                    binds: binds,
                    expr: expr,
                    span: sp,
                    exclusions: exclusions,
                    exclude_eof: false,
                    priority: priority,
                },
            ));
        }
        try!(parser.expect(&token::CloseDelim(token::Brace)));
        rules.insert(lhs, rhss);
    }
    let mut rules: BTreeMap<ast::Name, Vec<_>> = rules
        .into_iter()
        .map(|(lhs, rhss)| {
            let rhss = rhss.into_iter()
                .map(|(rule, act)| {
                    // figure out which symbols in `rule` are nonterminals vs terminals
                    let syms = rule.into_iter()
                        .zip(&act.binds)
                        .map(|(ident, bind)| {
                            if types.contains_key(&ident.0.name) {
                                Nonterminal(ident.0.name)
                            } else {
                                Terminal(TerminalPattern { ident: ident })
                            }
                        })
                        .collect();
                    Rhs {
                        syms: syms,
                        act: act,
                    }
                })
                .collect();
            (lhs, rhss)
        })
        .collect();
    let start = start.expect("need at least one nonterminal");
    let fake_start = symbol::Symbol::gensym("start");
    let unreachable = quote_expr!(cx, unreachable!());
    rules.insert(
        fake_start,
        vec![
            Rhs {
                syms: vec![Nonterminal(start)],
                act: Action {
                    binds: vec![],
                    expr: unreachable.clone(),
                    span: DUMMY_SP,
                    exclusions: BTreeSet::new(),
                    exclude_eof: false,
                    priority: -1,
                },
            },
        ],
    );
    let grammar = Grammar {
        rules: rules,
        start: fake_start,
    };
    let r = try!(
        lr1_machine(
            cx,
            &grammar,
            &types,
            token_ty,
            span_ty,
            range_fn_id,
            range_fn,
            name,
            |&TerminalPattern { ident, unit_like }, cx| {
                cx.pat(
                    DUMMY_SP,
                    if unit_like {
                        // `ident`
                        ast::PatKind::Path(None, cx.path_ident(DUMMY_SP, ident.0))
                    } else {
                        // `ident(..)`
                        ast::PatKind::TupleStruct(cx.path_ident(DUMMY_SP, ident.0), vec![], Some(0))
                    },
                )
            },
            |lhs, act, cx, syms| {
                let mut expr = act.expr.clone();
                let mut args = vec![];
                for (i, (x, sym)) in act.binds.iter().zip(syms.iter()).enumerate() {
                    args.push(match *x {
                        Binding::Pat(ref y) => Some(y.clone()),
                        Binding::Enum(sp, ref pats) => {
                            let id = gensym(&*format!("s{}", i));
                            let terminal = match *sym {
                                Nonterminal(..) => {
                                    cx.span_err(sp, "can't bind enum case to a nonterminal");
                                    gensym("error")
                                }
                                Terminal(x) => x.ident.0,
                            };
                            expr = cx.expr_match(
                                act.span,
                                cx.expr_ident(sp, id),
                                vec![
                                    cx.arm(
                                        sp,
                                        vec![
                                            cx.pat(
                                                sp,
                                                ast::PatKind::TupleStruct(
                                                    cx.path_ident(sp, terminal),
                                                    pats.clone(),
                                                    None,
                                                ),
                                            ),
                                        ],
                                        expr,
                                    ),
                                    quote_arm!(cx, _ => $unreachable,),
                                ],
                            );
                            let eid_pat = cx.pat_ident(sp, id);
                            let eid_expr = cx.expr_ident(sp, id);

                            // Workaround; closures sometimes complain about capturing from externals
                            // if we don't "let" themselves within the closure first
                            expr = quote_expr!(cx, { let $eid_pat = $eid_expr; $expr });
                            Some(cx.pat_ident(sp, id))
                        }
                        Binding::None => None,
                    });
                }

                // XXX: should be a cargo feature (?)
                if false {
                    let rule_str = pretty_rule(*lhs, syms);
                    let rule_str = &*rule_str;
                    expr = P(quote_expr!(cx, {
                    println!("reduce by {}", $rule_str);
                    $expr
                }).unwrap());
                }

                (expr, args, act.span)
            },
            |rhs, token| match token {
                Some(id) => !rhs.act.exclusions.contains(&id.to_string()),
                None => !rhs.act.exclude_eof,
            },
            |rhs, _| rhs.act.priority
        ).or_else(|conflict| match conflict {
            LR1Conflict::ReduceReduce {
                state,
                token,
                r1,
                r2,
            } => {
                let mut err = parser.diagnostic().struct_span_err(
                    sp,
                    &format!(
                        "reduce-reduce conflict:
state: {}
token: {}",
                        pretty(&state, "       "),
                        match token {
                            Some(id) => id.to_string(),
                            None => "EOF".to_string(),
                        }
                    ),
                );
                err.span_note(r1.1.act.span, "conflicting rule");
                err.span_note(r2.1.act.span, "conflicting rule");
                Err(err)
            }
            LR1Conflict::ShiftReduce { state, token, rule } => {
                let err = parser.diagnostic().struct_span_err(
                    rule.1.act.span,
                    &format!(
                        "shift-reduce conflict:
state: {}
token: {}",
                        pretty(&state, "       "),
                        match token {
                            Some(id) => id.to_string(),
                            None => "EOF".to_string(),
                        }
                    ),
                );
                Err(err)
            }
        })
    ).map(|mut item| {
        item.vis = visibility;
        item
    });
    Ok(base::MacEager::items(SmallVector::one(r)))
}

pub fn parser(tok: TokenStream) -> TokenStream {
    tok
}
