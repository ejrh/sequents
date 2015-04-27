:- multifile latex_name/2.

% Print the proof suitably for bussproof.sty
print_bussproof(tree(Sequent, SubProofs, RuleName, _Remarks, _Used, _Defined)) :-
    forall(member(SP, SubProofs), print_bussproof(SP)),
    length(SubProofs, N),
    print_bussproof_label(RuleName),
    print_bussproof_line(N, Sequent).

print_bussproof_label(axiom) :- !.
print_bussproof_label(RuleName) :-
    format('\\RightLabel{\\scriptsize $~l$}~n', RuleName).

print_bussproof_line(N, sequent(Ps, Qs)) :-
    get_bussproof_cmd(N, Cmd),
    get_predlist_str(Ps, PStr),
    get_predlist_str(Qs, QStr),
    format('~w{$~w \\vdash ~w$}~n', [Cmd, PStr, QStr]).

get_predlist_str([], '').
get_predlist_str([X], S) :- get_pred_str(X, S), !.
get_predlist_str([H|T], S) :-
    get_pred_str(H, S1),
    get_predlist_str(T, S2),
    format(atom(S), '~w, ~w', [S1, S2]).

get_pred_str(X, S) :-
    format(atom(S), '~l', X).

format_latex(_Arg, []) :-
    format('\\{ \\}'),
    !.
format_latex(_Arg, [H|T]) :-
    get_predlist_str(T, TStr),
    format('\\{ ~l, ~w \\}', [H, TStr]),
    !.
format_latex(_Arg, Term) :-
    Term =.. [F],
    try_latex_name(F, LatexF),
    format('~w', LatexF),
    !.
format_latex(_Arg, Term) :-
    Term =.. [F,X],
    current_op(Prec, fx, F),
    try_latex_name(F, LatexF),
    format_against_precedence(Prec, X, XStr),
    format('~w ~w', [LatexF, XStr]),
    !.
format_latex(_Arg, Term) :-
    Term =.. [F,X,Y],
    current_op(Prec, xfy, F),
    PrecP1 is Prec + 1,
    format_against_precedence(Prec, X, XStr),
    format_against_precedence(PrecP1, Y, YStr),
    try_latex_name(F, LatexF),
    format('~w ~w ~w', [XStr, LatexF, YStr]),
    !.
format_latex(_Arg, Term) :-
    Term =.. [F,X,Y],
    current_op(Prec, yfx, F),
    PrecP1 is Prec + 1,
    format_against_precedence(PrecP1, X, XStr),
    format_against_precedence(Prec, Y, YStr),
    try_latex_name(F, LatexF),
    format('~w ~w ~w', [XStr, LatexF, YStr]),
    !.
format_latex(_Arg, Term) :-
    Term =.. [F|Xs],
    try_latex_name(F, LatexF),
    get_predlist_str(Xs, XsStr),
    format('~w(~w)', [LatexF, XsStr]),
    !.
format_latex(_Arg, Term) :-
    format('<~w>', [Term]).

format_against_precedence(Prec, Term, S) :-
    get_precedence(Term, TermPrec),
    ((TermPrec < Prec) -> Fmt = '~l'; Fmt = '(~l)'),
    format(atom(S), Fmt, [Term]).

try_latex_name(Term, Name) :-
    latex_name(Term, Name), !.
try_latex_name(Term, Term).

:- format_predicate('l', format_latex(_, _)).

get_precedence(Term, Prec) :-
    Term =.. [F,_],
    current_op(Prec, fx, F),
    !.
get_precedence(Term, Prec) :-
    Term =.. [F,_,_],
    current_op(Prec, xfy, F),
    !.
get_precedence(_Term, 0).

get_bussproof_cmd(0, '\\AxiomC').
get_bussproof_cmd(1, '\\UnaryInfC').
get_bussproof_cmd(2, '\\BinaryInfC').
get_bussproof_cmd(3, '\\TrinaryInfC').
get_bussproof_cmd(4, '\\QuaternaryInfC').
get_bussproof_cmd(5, '\\QuinaryInfC').
