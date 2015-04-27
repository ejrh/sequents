%%%%% Symbols %%%%%

:- op(530, fx, agent).
:- op(530, fx, common).
:- op(540, xfy, knows).

latex_name(agent, '\\mathrm{agent}').
latex_name(common, '\\mathrm{common}').
latex_name(knows, '\\mathrm{knows}').

%%%%% Epistemic Logic %%%%%

simple_rule(knows_truth, [A knows P], P, []).
simple_rule(not_knows_false, [not P], not (A knows P), []).

simple_rule(knows_common, [common P], A knows P, []).

simple_rule(knows_common_trans, [common P], A knows B knows P, []).

%simple_rule(commonagent, [agent A, agent B], A knows agent B, []).

%simple_rule(knows_mp, [agent A, A knows P implies Q, A knows P], A knows Q, []).

simple_rule(knows_mt, [A knows P implies Q, A knows not Q], A knows not P, []).

%rule(system, sequent(Ps, Qs), [sequent([A knows Deduction|Ps], Qs)], [Name|Remarks], [agent A|Givens]) :-
%    member(agent A, Ps),
%    simple_rule(Name, Givens, Deduction, Remarks),
%    forall(member(G, Givens), member(A knows G, Ps)),
%    \+member(A knows Deduction, Ps).

%             P1, ..., P2   |-   C
% --------------------------------------------
% A knows P1, ..., A knows P2   |-   A knows C
rule(knows_system, sequent(Ps, Qs), [sequent(NewPs, NewQs)], [], [A knows Q|Knowledge]) :-
    Qs = [A knows Q],
    NewQs = [Q],
    findall(Knowledge, (member(K, Ps), K = A knows _), NewPs),
    findall(P, member(A knows P, Ps), NewPs).

rule(knows_oneof, sequent(Ps, Qs), [Prem], [], [A knows (F=X)]) :-
    member(A knows (F=X), Ps),
    add_left(A knows F, sequent(Ps, Qs), Prem).

%rule(knows_not_oneof, sequent(Ps, Qs), [Prem], [], [A knows F oneof Vs, A knows (F=X)]) :-
%    member(A knows F oneof Vs, Ps),
%    member(A knows (F=X), Ps),
%    add_left(A knows F, sequent(Ps, Qs), Prem).
