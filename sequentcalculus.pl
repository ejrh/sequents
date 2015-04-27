% rule(Name, Conclusion, Premises, Remarks, Used)
:- multifile rule/5.
:- multifile simple_rule/4.

:- op(500, xfx, sequent).

try_rule(Name, Sequent, SortedPremises, Remarks, Used, Defined) :-
    rule(Name, Sequent, Premises, Remarks, Used),
    maplist(sort_sequent, Premises, SortedPremises),
    \+member(Sequent, SortedPremises),
    maplist(extract_defined(Sequent), Premises, Defined).

sort_sequent(sequent(Ps, Qs), sequent(NewPs, NewQs)) :-
    msort(Ps, NewPs),
    msort(Qs, NewQs).

extract_defined(sequent(Ps, Qs), sequent(NewPs, NewQs), Defined) :-
    subtract(NewPs, Ps, DefinedPs),
    subtract(NewQs, Qs, DefinedQs),
    union(DefinedPs, DefinedQs, Defined).

prove(Sequent) :-
    try_rule(_Name, Sequent, Premises, _Remarks, _Used, _Defined),
    forall(member(P, Premises), prove(P)).

proof(0, Sequent, tree(Sequent, [limit])) :- fail.
proof(Depth, Sequent, tree(Sequent, SubProofs, RuleName, Remarks, Used, Defined)) :-
    Depth > 1,
    try_rule(RuleName, Sequent, Premises, Remarks, Used, Defined),
    NewDepth is Depth - 1,
    maplist(proof(NewDepth), Premises, SubProofs).
proof(_Depth, Sequent, tree(Sequent, [norule])) :-
    \+try_rule(_RuleName, Sequent, _Premises, _Remarks, _Used, _Defined), fail.

%%%%% Proof simplification

% Make a proof simpler by removing unused predicates
% p and q   -->   q   (andleft1, used p and q)
%   p, p and q   -->   q   (andleft2, used p and q; p stripped)
%     p, q, p and q   -->   q   (axiom, used q; p, p and q stripped)

simplify_proof(tree(sequent(Ps, Qs), SubProofs, RuleName, Remarks, Used, Defined),
        tree(sequent(NewPs, NewQs), NewSubProofs, RuleName, Remarks, AllUsed, Defined)) :-
    maplist(simplify_proof, SubProofs, NewSubProofs),
    findall(U, member(tree(_, _, _, _, U, _), NewSubProofs), SubUsed),
    foldl(union, SubUsed, Used, AllUsed),
    intersection(Ps, AllUsed, NewPs),
    intersection(Qs, AllUsed, NewQs).

% Make a proof simpler by removing unnecessary steps
% p and q   -->   q   (andleft1, defined p; p not used hence step is stripped)
%   p and q   -->   q   (andleft2, defined q)
%     q   -->   q   (axiom, used q)
streamline_proof(tree(sequent(Ps, Qs), SubProofs, RuleName, Remarks, Used, Defined),
        tree(sequent(NewPs, NewQs), NewSubProofs, RuleName, Remarks, Used, Defined)) :-
    \+maplist(check_void_intersection, SubProofs, Defined),
    NewPs = Ps,
    NewQs = Qs,
    NewSubProofs = SubProofs.

check_void_intersection(tree(_, _, _, _, Used, _), Defined) :-
    intersection(Used, Defined, []).

%%%%% Printing proofs %%%%%

print_proof(Proof) :-
    print_proof(Proof, 0).

print_proof(tree(Sequent, SubProofs, RuleName, Remarks, _Used, _Defined), Indent) :-
    print_indent(Indent),
    format_sequent(Sequent, SequentStr),
    format('~w    ~w~n', [SequentStr, [RuleName|Remarks]]),
    NewIndent is Indent + 1,
    forall(member(P, SubProofs), print_proof(P, NewIndent)).

print_proof(tree(Sequent, Remarks), Indent) :-
    print_indent(Indent),
    format_sequent(Sequent, SequentStr),
    format('~w    ~w~n', [SequentStr, Remarks]).

format_sequent(sequent(Ps, Qs), S) :-
    format(atom(S), '~w   sequent   ~w', [Ps, Qs]).

print_indent(0) :- !.
print_indent(Indent) :-
    format('  '),
    NewIndent is Indent - 1,
    print_indent(NewIndent).

%%%%% Rule helpers %%%%%

add_left(P, sequent(Ps, Qs), sequent([P|Ps], Qs)) :-
    var(P); \+member(P, Ps).

add_right(Q, sequent(Ps, Qs), sequent(Ps, [Q|Qs])) :-
    var(Q); \+member(Q, Qs).

rule(RuleName, sequent(Ps, Qs), [sequent([Deduction|Ps], Qs)], Remarks, Givens) :-
    simple_rule(RuleName, Givens, Deduction, Remarks),
    subset(Givens, Ps),
    \+member(Deduction, Ps).
