/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/annotation.h"
#include "library/constants.h"
#include "library/quote.h"
#include "library/io_state_stream.h"
#include "library/trace.h"
#include "library/typed_expr.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "kernel/scope_pos_info_provider.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_parser.h"
#include "library/vm/vm_name.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/tactic_evaluator.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/tactic_notation.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/builtin_exprs.h"
#include "util/sexpr/option_declarations.h"

#define LEAN_PARSER_DEFAULT_TACTIC_TYPE "ttactic"

/* Interactive tactic notation used by 'by', 'begin ... end' and '`[...]` tactic quotation blocks.
 * It supports all tactic types that implement 'monad_interactive_tactic'. */
namespace lean {
static name * g_parser_default_tactic_type = nullptr;

static name get_parser_default_tactic_type(options const & opts) {
    return opts.get_string(*g_parser_default_tactic_type, LEAN_PARSER_DEFAULT_TACTIC_TYPE);
}

static expr mk_tactic_step(parser & p, expr tac, pos_info const & pos) {
    if (tac.get_tag() == nulltag)
        tac = p.save_pos(tac, pos);
    return p.save_pos(mk_app(mk_constant(get_monad_interactive_tactic_step_name()), tac), pos);
}

static expr mk_tactic_istep(parser & p, expr tac, pos_info const & pos0, pos_info const & pos) {
    if (p.in_notation())
        return mk_tactic_step(p, tac, pos);
    if (tac.get_tag() == nulltag)
        tac = p.save_pos(tac, pos);
    // compute a fingerprint of the pre-execution state: the tactic's preterm and the environment fingerprint
    uint64 h = hash(static_cast<uint64>(tac.hash()), get_fingerprint(p.env()));
    expr memoize = mk_app(mk_constant(get_monad_interactive_tactic_memoize_name()), mk_prenum(mpz(h)), tac);
    expr istep = mk_app({mk_constant(get_monad_interactive_tactic_istep_name()),
            mk_prenum(mpz(pos0.first)), mk_prenum(mpz(pos0.second)),
            mk_prenum(mpz(pos.first)), mk_prenum(mpz(pos.second)),
            p.save_pos(memoize, pos)});
    return p.save_pos(istep, pos);
}

static expr mk_tactic_step(parser & p, expr tac, pos_info const & pos0, pos_info const & pos, bool use_istep) {
    if (use_istep)
        return mk_tactic_istep(p, tac, pos0, pos);
    else
        return mk_tactic_step(p, tac, pos);
}

static expr mk_tactic_save_info(parser & p, pos_info const & pos) {
    auto pos_e = mk_anonymous_constructor(mk_app(mk_expr_placeholder(),
                                                 mk_prenum(mpz(pos.first)),
                                                 mk_prenum(mpz(pos.second))));
    return p.save_pos(mk_app(mk_constant(get_monad_interactive_tactic_save_info_name()), pos_e), pos);
}

static expr mk_tactic_solve1(parser & p, expr tac, pos_info const & pos0, pos_info const & pos, bool use_istep) {
    if (tac.get_tag() == nulltag)
        tac = p.save_pos(tac, pos);
    expr r = p.save_pos(mk_app(mk_constant(get_monad_interactive_tactic_solve1_name()), tac), pos);
    if (use_istep)
        r = mk_tactic_istep(p, r, pos0, pos);
    return r;
}

static expr concat(parser & p, expr const & tac1, expr const & tac2, pos_info const & pos) {
    return p.save_pos(mk_app(mk_constant(get_has_bind_seq_name()), tac1, tac2), pos);
}

optional<name> get_interactive_tactic_full_name(environment const & env, options const & opts, name const & tac_class,
                                                name const & tac) {
    vm_state S(env, opts);
    tactic_state s = mk_tactic_state_for(env, opts, "_tactic_notation", local_context(), mk_true());
    if (env.find(get_resolve_interactive_tactic_name())) {
        auto r = S.invoke(get_resolve_interactive_tactic_name(), {to_obj(s), to_obj(tac), to_obj(tac_class)});
        if (tactic::is_result_success(r))
            return some(to_name(tactic::get_result_value(r)));
    }
    return optional<name>();
}

static bool is_curr_exact_shortcut(parser & p) {
    return p.curr_is_token(get_calc_tk());
}

static optional<name> is_interactive_tactic(parser & p, name const & tac_class) {
    name id;
    switch (p.curr()) {
        case token_kind::Identifier:
            id = p.get_name_val();
            break;
        case token_kind::Keyword:
            id = p.get_token_info().value();
            break;
        default:
            return {};
    }
    return get_interactive_tactic_full_name(p.env(), p.get_options(), tac_class, id);
}

static optional<name> is_tactic_type(environment const & env, name const & n) {
    type_context ctx(env);
    local_context lcx;
    expr tac_class = mk_app(mk_constant(get_monad_interactive_tactic_name()),
            /* config */ ctx.mk_metavar_decl(lcx, mk_sort(mk_level_one())),
                            mk_constant(n));
    if (ctx.mk_class_instance(tac_class)) {
        return optional<name>(n);
    } else {
        return optional<name>();
    }
}

/** Recognizes "short" tactic type names.
    TODO(Sebastian): This is too ad hoc. */
static optional<name> is_tactic_class(environment const & env, name const & n) {
    if (n == "smt")
        return optional<name>(name("smt_tactic"));
    return is_tactic_type(env, n);
}

static expr parse_begin_end_block(parser & p, pos_info const & start_pos, name const & end_token,
                                  optional<name> tac_class = optional<name>(), bool use_istep = true,
                                  bool use_solve1 = false);

static expr parse_nested_interactive_tactic(parser & p, name const & tac_class, bool use_istep, bool use_solve1) {
    auto pos = p.pos();
    if (p.curr_is_token(get_lcurly_tk())) {
        return parse_begin_end_block(p, pos, get_rcurly_tk(), some(tac_class), use_istep, use_solve1);
    } else if (p.curr_is_token(get_begin_tk())) {
        return parse_begin_end_block(p, pos, get_end_tk(), some(tac_class), use_istep, use_solve1);
    } else {
        return p.parser_error_or_expr({"invalid nested auto-quote tactic, '{' or 'begin' expected", pos});
    }
}

static expr parse_interactive_tactic(parser & p, name const & decl_name, name const & tac_class, bool use_istep) {
    auto pos = p.pos();
    expr type     = p.env().get(decl_name).get_type();
    buffer<expr> args;
    try {
        try {
            p.next();
            while (is_pi(type)) {
                p.check_break_before();
                if (is_explicit(binding_info(type))) {
                    expr arg_type = binding_domain(type);
                    if (is_app_of(arg_type, get_interactive_parse_name())) {
                        parser::quote_scope scope(p, true);
                        args.push_back(parse_interactive_param(p, arg_type));
                    } else if (is_app_of(arg_type, get_interactive_parse_tactic_name(), 2)) {
                        bool use_solve1 = app_arg(arg_type) == mk_bool_tt();
                        expr tac_type   = app_arg(app_fn(arg_type));
                        auto new_tac_class = tac_class;
                        if (is_constant(tac_type))
                            new_tac_class = const_name(tac_type);
                        auto tac = parse_nested_interactive_tactic(p, new_tac_class, use_istep, use_solve1);
                        args.push_back(tac);
                    } else {
                        break;
                    }
                }
                type = binding_body(type);
            }
            while (p.curr_lbp() >= get_max_prec()) {
                p.check_break_before();
                args.push_back(p.parse_expr(get_max_prec()));
            }
            p.check_break_before();
        } catch (break_at_pos_exception) {
            throw;
        } catch (...) {
            p.check_break_before();
            throw;
        }
    } catch (break_at_pos_exception & e) {
        e.m_token_info.m_tac_param_idx = args.size();
        throw;
    }
    expr r = p.mk_app(p.save_pos(mk_constant(decl_name), pos), args, pos);
    return mk_tactic_step(p, r, pos, pos, use_istep);
}

static expr mk_tactic_unit(name const & tac_class) {
    return mk_app(mk_constant(tac_class), mk_constant(get_unit_name()));
}

struct parse_tactic_fn {
    parser & m_p;
    name     m_tac_class;
    bool     m_use_istep;

    parse_tactic_fn(parser & p, name tac_class, bool use_istep):
        m_p(p), m_tac_class(tac_class), m_use_istep(use_istep) {}

    expr concat(expr const & tac1, expr const & tac2, pos_info const & pos) {
        return ::lean::concat(m_p, tac1, tac2, pos);
    }

    expr andthen(expr const & tac1, expr const & tac2, pos_info const & pos) {
        /* HACK(Sebastian): The heterogeneous andthen operator is problematic for type inference and
         * will likely be replaced by separate notations in the future. Until then, we pass the
         * type arguments explictly here. */
        expr lhs = mk_tactic_unit(m_tac_class);
        expr rhs = is_typed_expr(tac2) ? get_typed_expr_type(tac2) : lhs;
        expr r = m_p.save_pos(mk_app(
                mk_app(mk_explicit(mk_constant(get_has_andthen_andthen_name())), lhs, rhs, lhs, mk_expr_placeholder()),
                tac1, tac2), pos);
        if (m_use_istep)
            r = mk_tactic_istep(m_p, r, pos, pos);
        return r;
    }

    expr orelse(expr const & tac1, expr const & tac2, pos_info const & pos) {
        return m_p.save_pos(mk_app(mk_constant(get_has_orelse_orelse_name()), tac1, tac2), pos);
    }

    expr parse_qexpr(unsigned rbp = 0) {
        auto p = m_p.pos();
        parser::quote_scope scope1(m_p, true);
        restore_decl_meta_scope scope2;
        expr e = m_p.parse_expr(rbp);
        return m_p.save_pos(mk_pexpr_quote_and_substs(e, /* is_strict */ false), p);
    }

    expr parse_elem_core(bool save_info) {
        try {
            m_p.check_break_before();
            if (m_p.curr_is_identifier())
                m_p.check_break_at_pos();
        } catch (break_at_pos_exception & e) {
            e.m_token_info.m_context   = break_at_pos_exception::token_context::interactive_tactic;
            e.m_token_info.m_param     = m_tac_class;
            throw;
        }
        expr r;
        auto pos = m_p.pos();
        if (auto dname = is_interactive_tactic(m_p, m_tac_class)) {
            try {
                r = parse_interactive_tactic(m_p, *dname, m_tac_class, m_use_istep);
            } catch (break_at_pos_exception & e) {
                if (!m_p.get_complete() &&
                    (!e.m_token_info.m_token.size() ||
                     e.m_token_info.m_context == break_at_pos_exception::token_context::none)) {
                    e.m_token_info.m_pos       = pos;
                    e.m_token_info.m_token     = dname->get_string();
                    e.m_token_info.m_context   = break_at_pos_exception::token_context::interactive_tactic;
                    e.m_token_info.m_param     = m_tac_class;
                }
                throw;
            }
        } else if (is_curr_exact_shortcut(m_p)) {
            expr arg = parse_qexpr();
            if (auto exact_name = get_interactive_tactic_full_name(m_p.env(), m_p.get_options(), m_tac_class, "exact")) {
                r = m_p.mk_app(m_p.save_pos(mk_constant(*exact_name), pos), arg, pos);
                if (m_use_istep) r = mk_tactic_istep(m_p, r, pos, pos);
            } else {
                return m_p.parser_error_or_expr(parser_error("invalid interactive tactic, tactic type must support "
                                                             "an 'exact' tactic.", pos));
            }
        } else {
            r = m_p.parse_expr();
            if (m_use_istep) r = mk_tactic_istep(m_p, r, pos, pos);
        }
        if (save_info)
            return concat(mk_tactic_save_info(m_p, pos), r, pos);
        else
            return r;
    }

    expr parse_block(pos_info const & pos, name const & end_tk) {
        return ::lean::parse_begin_end_block(m_p, pos, end_tk, optional<name>(m_tac_class), m_use_istep);
    }

    expr parse_elem(bool save_info, bool use_solve1 = true) {
        if (m_p.curr_is_token(get_begin_tk()) ||
            m_p.curr_is_token(get_lcurly_tk())) {
            auto pos = m_p.pos();
            name const & end_tk = m_p.curr_is_token(get_begin_tk()) ? get_end_tk() : get_rcurly_tk();
            expr next_tac = parse_block(pos, end_tk);
            auto end_pos = m_p.pos_of(next_tac);
            if (use_solve1) {
                next_tac       = mk_tactic_solve1(m_p, next_tac, pos, end_pos, m_use_istep && save_info);
            }
            if (save_info) {
                expr info_tac = mk_tactic_save_info(m_p, pos);
                return concat(info_tac, next_tac, pos);
            } else {
                return next_tac;
            }
        } else if (m_p.curr_is_token(get_lbracket_tk())) {
            auto pos = m_p.pos();
            m_p.next();
            buffer<expr> args;
            if (!m_p.curr_is_token(get_rbracket_tk())) {
                while (true) {
                    args.push_back(parse_elem(save_info, false));
                    if (!m_p.curr_is_token(get_comma_tk()))
                        break;
                    m_p.next();
                }
            }
            m_p.check_token_next(get_rbracket_tk(), "invalid tactic list, ']' expected");
            expr r = mk_lean_list(m_p, args, pos);
            expr type = mk_app(mk_constant(get_list_name()), mk_tactic_unit(m_tac_class));
            r = m_p.save_pos(mk_typed_expr(type, r), pos);
            return r;
        } else {
            if (m_p.curr_is_token(get_by_tk())) {
                // `by tac` ~> `solve1 { tac }`
                m_p.next();
                auto pos = m_p.pos();
                expr tac = operator()(save_info);
                auto end_pos = m_p.pos_of(tac);
                tac = mk_tactic_solve1(m_p, tac, pos, end_pos, m_use_istep && save_info);
                if (save_info) {
                    expr info_tac = mk_tactic_save_info(m_p, pos);
                    return concat(info_tac, tac, pos);
                } else {
                    return tac;
                }
            } else {
                return parse_elem_core(save_info);
            }
        }
    }

    expr parse_orelse(expr left) {
        auto start_pos = m_p.pos();
        expr r = left;
        while (m_p.curr_is_token(get_orelse_tk())) {
            m_p.next();
            expr curr = parse_elem(false);
            r         = orelse(r, curr, start_pos);
        }
        return r;
    }

    expr parse_andthen(expr left) {
        auto start_pos = m_p.pos();
        expr r = left;
        while (m_p.curr_is_token(get_semicolon_tk())) {
            m_p.next();
            expr curr = parse_elem(false);
            if (m_p.curr_is_token(get_orelse_tk()))
                curr = parse_orelse(curr);
            r = andthen(r, curr, start_pos);
        }
        return r;
    }

    expr operator()(bool save_info = true) {
        expr r = parse_elem(save_info);
        if (m_p.curr_is_token(get_semicolon_tk()))
            return parse_andthen(r);
        else if (m_p.curr_is_token(get_orelse_tk()))
            return parse_orelse(r);
        else
            return r;
    }
};

static expr parse_tactic_core(parser & p, name const & tac_class, bool use_istep) {
    return parse_tactic_fn(p, tac_class, use_istep)();
}

static expr parse_tactic(parser & p, name const & tac_class, bool use_istep) {
    if (p.in_quote()) {
        parser::quote_scope _(p, false);
        return parse_tactic_core(p, tac_class, use_istep);
    } else {
        return parse_tactic_core(p, tac_class, use_istep);
    }
}

static optional<name> parse_tactic_class(parser & p) {
    if (p.curr_is_token(get_lbracket_tk())) {
        p.next();
        auto id_pos = p.pos();
        name id = p.check_id_next("invalid 'begin [...] ... end' block, identifier expected");
        auto new_class = is_tactic_class(p.env(), id);
        if (!new_class) {
            p.maybe_throw_error({sstream() << "invalid 'begin [" << id << "] ...end' block, "
                               << "'" << id << "' is not a valid tactic class", id_pos});
            return optional<name>();
        }
        p.check_token_next(get_rbracket_tk(), "invalid 'begin [...] ... end block', ']' expected");
        return new_class;
    } else {
        return optional<name>();
    }
}

struct parse_begin_end_block_fn {
    parser &       m_p;
    optional<name> m_tac_class;
    bool           m_use_istep;

    parse_begin_end_block_fn(parser & p, optional<name> tac_class, bool use_istep):
        m_p(p), m_tac_class(tac_class), m_use_istep(use_istep) {}

    expr concat(expr const & tac1, expr const & tac2, pos_info const & pos) {
        return ::lean::concat(m_p, tac1, tac2, pos);
    }

    expr concat(buffer<expr> const & args, unsigned start, unsigned end, pos_info const & pos) {
        lean_assert(start < end);
        lean_assert(end <= args.size());
        if (end == start+1)
            return args[start];
        unsigned mid = (start + end)/2;
        expr left  = concat(args, start, mid, pos);
        expr right = concat(args, mid, end, pos);
        return concat(left, right, pos);
    }

    expr concat(buffer<expr> const & args, pos_info const & pos) {
        lean_assert(!args.empty());
        return concat(args, 0, args.size(), pos);
    }

    expr mk_save_info() {
        expr r = mk_tactic_save_info(m_p, {m_p.pos().first, m_p.pos().second + 1});
        return r;
    }

    expr parse_tactic() {
        return ::lean::parse_tactic(m_p, *m_tac_class, m_use_istep);
    }

    expr operator()(pos_info const & start_pos, name const & end_token, bool use_solve1) {
        auto sync = [&] {
            while (!m_p.curr_is_token(get_comma_tk()) && !m_p.curr_is_token(end_token) &&
                    !m_p.curr_is_token(get_semicolon_tk()) && !m_p.curr_is_token(get_orelse_tk())) {
                auto pos0 = m_p.pos();
                m_p.next();
                if (m_p.pos() == pos0) break;
            }
            if (!m_p.curr_is_token(get_end_tk())) m_p.next();
            m_p.maybe_throw_error({"sync", m_p.pos()});
        };

        m_p.next();
        optional<name> old_tac_class = m_tac_class;
        optional<name> new_tac_class = parse_tactic_class(m_p);
        optional<expr> cfg;
        if (new_tac_class && m_p.curr_is_token(get_with_tk())) {
            m_p.next();
            cfg = m_p.parse_expr();
            m_p.check_token_next(get_comma_tk(), "invalid begin [...] with cfg, ... end block, ',' expected");
        }
        if (new_tac_class)
            m_tac_class = new_tac_class;
        if (!m_tac_class)
            m_tac_class = get_parser_default_tactic_type(m_p.get_options());
        buffer<expr> to_concat;
        to_concat.push_back(mk_tactic_save_info(m_p, start_pos));
        while (!m_p.curr_is_token(end_token)) {
            pos_info pos = m_p.pos();
            try {
                to_concat.push_back(parse_tactic());
                if (!m_p.curr_is_token(end_token)) {
                    m_p.without_break_at_pos<void>([&]() {
                        if (!m_p.check_token_next(get_comma_tk(), "invalid 'begin-end' expression, ',' expected")) {
                            sync();
                        }
                    });
                }
                to_concat.push_back(mk_save_info());
            } catch (break_at_pos_exception & ex) {
                ex.report_goal_pos(pos);
                throw;
            }
            if (m_p.pos() == pos) sync();
            if (m_p.pos() == pos) break;
        }
        auto end_pos = m_p.pos();
        expr r = concat(to_concat, start_pos);
        r = concat(r, mk_tactic_save_info(m_p, end_pos), end_pos);
        if (use_solve1)
            r = mk_tactic_solve1(m_p, r, start_pos, end_pos, m_use_istep);
        try {
            m_p.next();
        } catch (break_at_pos_exception & ex) {
            ex.report_goal_pos(end_pos);
            throw;
        }
        if (old_tac_class == m_tac_class) {
            /* Nested block with unchanged tactic type. We fix the type of `r` to
             * avoid unification issues. For example, if `r` is a universe-polymorphic
             * tactic of type `?m unit` and passed to `try : parse_tactic tactic -> tactic unit`,
             * we would create the problematic unification problem `?m unit =?= parse_tactic tactic`.
             * The typed_expr breaks this problem down into `?m unit =?= tactic unit` and
             * `tactic unit = parse_tactic tactic`. */
            return copy_tag(r, mk_typed_expr(mk_tactic_unit(*m_tac_class), r));
        } else {
            expr e_cfg = cfg ? mk_app(mk_constant(get_option_some_name()), *cfg) : mk_constant(get_option_none_name());
            return copy_tag(r, mk_app(mk_constant(get_execute_interactive_tactic_name()), mk_constant(*m_tac_class), e_cfg, r));
        }
    }
};

static expr parse_begin_end_block(parser & p, pos_info const & start_pos, name const & end_token, optional <name> tac_class,
                                  bool use_istep, bool use_solve1) {
    return parse_begin_end_block_fn(p, tac_class, use_istep)(start_pos, end_token, use_solve1);
}

expr parse_begin_end_expr_core(parser & p, pos_info const & pos, name const & end_token) {
    parser::local_scope scope1(p);
    meta_definition_scope scope2;
    p.clear_expr_locals();
    expr tac = parse_begin_end_block(p, pos, end_token);
    return copy_tag(tac, mk_by(tac));
}

expr parse_begin_end_expr(parser & p, pos_info const & pos) {
    return parse_begin_end_expr_core(p, pos, get_end_tk());
}

expr parse_curly_begin_end_expr(parser & p, pos_info const & pos) {
    return parse_begin_end_expr_core(p, pos, get_rcurly_tk());
}

expr parse_begin_end(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_begin_end_expr(p, pos);
}

expr parse_by(parser & p, unsigned, expr const *, pos_info const & pos) {
    p.next();
    parser::local_scope scope1(p);
    meta_definition_scope scope2;
    p.clear_expr_locals();
    auto tac_pos = p.pos();
    try {
        bool use_istep = true;
        name tac_class = get_parser_default_tactic_type(p.get_options());
        expr tac  = parse_tactic(p, tac_class, use_istep);
        expr type = mk_tactic_unit(tac_class);
        tac = p.save_pos(mk_typed_expr(type, tac), tac_pos);
        // execute `tac`: convert to `tactic unit`
        tac = p.save_pos(mk_app(mk_constant(get_execute_interactive_tactic_name()),
                                mk_constant(tac_class),
                                mk_constant(get_option_none_name()), // no config
                                tac),
                         tac_pos);
        return p.save_pos(mk_by(tac), pos);
    } catch (break_at_pos_exception & ex) {
        ex.report_goal_pos(tac_pos);
        throw ex;
    }
}

/*
Consider the following example:

  meta def apply_zero_add (a : pexpr) : tactic unit :=
  `[apply zero_add %%a] -- We don't want the error to be reported here when 'a' does not have the expected type.

  example (a : nat) : 0 + a = a :=
  begin
    apply_zero_add `(tt), -- Error should be here
  end

We address the issue above by erasing position information from quoted terms nested in 'e'.
*/
static void erase_quoted_terms_pos_info(parser & p, expr const & e) {
    for_each(e, [&](expr const & e, unsigned) {
            if (is_pexpr_quote(e)) {
                for_each(get_pexpr_quote_value(e), [&](expr const & e, unsigned) {
                        p.erase_pos(e);
                        return true;
                    });
            }
            return true;
        });
}

expr parse_interactive_tactic_block(parser & p, unsigned, expr const *, pos_info const & pos) {
    name const & tac_class = get_parser_default_tactic_type(p.get_options());
    bool use_istep    = false;
    expr r = parse_begin_end_block(p, pos, get_rbracket_tk(), some(tac_class), use_istep);
    erase_quoted_terms_pos_info(p, r);
    return r;
}

void initialize_tactic_notation() {
    g_parser_default_tactic_type = new name({"parser", "default_tactic_type"});
    register_string_option(*g_parser_default_tactic_type, LEAN_PARSER_DEFAULT_TACTIC_TYPE,
                           "(parser) default tactic type to use for interactive tactic scripts");
}

void finalize_tactic_notation() {
    delete g_parser_default_tactic_type;
}
}
