% =================================
% = Displacement calculus grammar =
% =================================

% This grammar is a version of the file "d_grammar.pl" with the
% addition of case for noun phrases. As the original "d_grammar.pl"
% this grammar contains many examples from
%
% Glyn Morrill, Oriol Valentin and Mario Fadda (2011),
% The Displacement Calculus, Journal of Logic, Language
% and Information 20, p. 1-48.

% define operators to allow for easier specification of
% displacement calculus lexical entries.
%
% WARNING: in case of doubt, use parentheses to disambiguate!
% I have deliberately not changed the definitions of standard
% mathematical and logical operations of Prolog, notably |
% (alternative of ; for use in DCG), / and *.
%
% This means for example that:
% c/d*b/c = ((c/d)*b)/c
% which corresponds to a left-to-right evaluation of the
% mathematical functions of division and multiplication.
% However, we do have the familiar a/b/c = (a/b)/c and
% c\b\a = (c\(b\a) and even a\b/c = (a\b)/c.

:- op(400, xfy, \).
:- op(400, xfy, \>).  % = \downarrow_>
:- op(400, yfx, />).  % = \uparrow_>
:- op(400, xfy, \<).  % = \downarrow_<
:- op(400, yfx, /<).  % = \uparrow_>
:- op(400, yfx, *<).  % = \odot_<
:- op(400, yfx, *>).  % = \odot_>


:- abolish(lex/3), abolish(lex/4), abolish(lex/5), abolish(test/1), abolish(atomic_formula/1), abolish(atomic_formula/3), abolish(macro/2).

atomic_formula(n(_,_,_)).

% =======================
% =  Example Sentences  =
% =======================


test(0) :-
	parse([mary,gave,john,the_cold_shoulder], s).
test(1) :-
	parse([john,gave,every,book,to,mary], s).
test(2) :-
	parse([john,gave2,every,book,to,mary], s).
test(3) :-
	parse([mary,thinks,someone,left], s).
test(4) :-
	parse([everyone,loves,someone], s).
test(5) :-
	parse([john,slept,before,mary,did], s).
test(6) :-
	parse([dog,that,mary,saw,today], cn).
test(7) :-
	parse([bagels,which,john,sold,for,ten_million_dollars], cn).
test(8) :-
	parse([mountain,the,painting,of,which,by,cezanne,john,sold,for,ten_million_dollars], cn).
test(9) :-
	parse([john,who,jogs,sneezed], s).
test(10) :-
	parse([john,studies,logic,and,charles,phonetics], s).
test(11) :-
	parse([john,ate,more,donuts,than,mary,bought,bagels], s).
test(12) :-
	parse([dat,jan,boeken,las], cs).
test(13) :-
	parse([dat,jan,boeken,kan,lezen], cs).
test(14) :-
	parse([dat,jan,boeken,wil,kunnen,lezen], cs).
test(15) :-
	parse([dat,jan,alles,las], cs).
test(16) :-
	parse([dat,jan,alles,kan,lezen], cs).
test(17) :-
	parse([dat,jan,cecilia,de,nijlpaarden,zag,voeren], cs).
test(18) :-
	parse([dat,jan,cecilia,henk,de,nijlpaarden,zag,helpen,voeren], cs).
test(19) :-
	parse([wil2,jan,boeken,lezen], q).
test(20) :-
	parse([jan,wil2,boeken,lezen], n(A,B,C)*(^(q/<n(A,B,C)))).
test(201) :-
	parse([boeken,wil2,jan,lezen], n(A,B,C)*(^(q/<n(A,B,C)))).
test(21) :-
	parse([john,bought,himself,coffee], s).
test(22) :-
	parse([every,man,loves,himself], s).
% There is a subtle difference between the Displacement calculus formulas and their first-order linear logic
% translations for these two cases; we cannot uniquely recover the D formula for "himself2" from its linear
% logic translation; the linear logic formula leaves the order of the two hypothetical np undetermined,
% whereas the D formula requires the word "himself2" to occur after the other hypothetical np. I'm working
% on aligning the linear logic and D analysis on this point, but it seems this distinction of D has
% limited applications and is actually a disadvantage with respect to first-order linear logic when it comes
% to the treatment of quantification inside Dutch verb clusters (the discussion on page 28 of Morrill e.a., 2011
% briefly mentions the necessity for duplicating separators and connectives).
test(23) :-
	parse([mary,talked,to,john,about,himself2], s).
test(24) :-
	parse([mary,talked,about,himself2,to,john], s).

% =======================
% =       Macros        =
% =======================

macro(d_q, ((s/<n(_,_,_))\<s)/cn).
macro(d_tv(A,B,C), (n(A,B,C)\s)/n(_,_,_)).
macro(d_vp(A,B,C), n(A,B,C)\s).


% =======================
% =       Lexicon       =
% =======================

% = lex(+Word, +Formula, +Semantics)

lex(john, n(sg,3,m), j).
lex(mary, n(sg,3,f), m).
lex(charles, n(sg,3,m), c).
lex(logic, n(sg,3,n), l).
lex(phonetics, n(sg,3,n), p).
lex(cezanne, n(sg,3,m), cezanne).
lex(coffee, n(sg,3,n), coffee).
lex(the, n(_,_,_)/cn, iota).
lex(ten_million_dollars, n(pl,3,_), '\\$10.000.000'). % double backslash necessary here to ensure correct LaTeX operation
lex(thinks, (n(sg,3,_)\s)/s, think).
lex(left, n(_,_,_)\s, leave).
lex(slept, n(_,_,_)\s, sleep).
lex(jogs, n(sg,3,_)\s, jog).
lex(sneezed, n(_,_,_)\s, sneeze).
lex(loves, (n(sg,3,_)\s)/n(_,_,_), love).
lex(saw, (n(_,_,_)\s)/n(_,_,_), see).
lex(studies, (n(sg,3,_)\s)/n(_,_,_), study).
lex(ate, d_tv(_,_,_), eat).
lex(bought, d_tv(_,_,_), buy).
lex(bought, (d_tv(_,_,_))/n(_,_,_), buy).
lex(talked, ((n(_,_,_)\s)/pp)/pp, talk).
lex(today, (n(A,B,C)\s)\(n(A,B,C)\s), lambda(VP,lambda(N,appl(today,appl(VP,N))))).
lex(gave, (n(_,_,_)\s)/(n(_,_,_)*pp), lambda(Pair,lambda(X,appl(appl(appl(g,pi2(Pair)),pi1(Pair)),X)))).
lex(gave, lproj(((n(_,_,_)\s)/<n(_,_,_))/tcs), lambda(_TCS,shun)).
lex(the_cold_shoulder, tcs, tcs).
lex(gave2, ((n(_,_,_)\s)/pp)/n(_,_,_), give).
lex(sold, ((n(_,_,_)\s)/pp)/n(_,_,_), sell_for).
lex(book, cn, b).
lex(dog, cn, dog).
lex(man, cn, man).
lex(donuts, cn, donuts).
lex(bagels, cn, bagels).
lex(mountain, cn, mountain).
lex(painting, cn/pp, painting_of).
lex(of, pp/n(_,_,_), lambda(X,X)).
lex(by, (cn\cn)/n(_,_,_), lambda(NP,lambda(N,lambda(X,bool(appl(N,X),&,appl(appl(by,NP),X)))))).
lex(for, pp/n(_,_,_), lambda(X,X)).
lex(to, pp/n(_,_,_), lambda(X,X)).
lex(about, pp/n(_,_,_), lambda(X,X)).
lex(a, d_q, lambda(X,lambda(Y,quant(exists,Z,bool(appl(X,Z),&,appl(Y,Z)))))).
lex(every, d_q, lambda(X,lambda(Y,quant(forall,Z,bool(appl(X,Z),->,appl(Y,Z)))))).
lex(someone, (s/>n(_,_,_))\<s, lambda(P,quant(exists,X,appl(P,X)))).
lex(everyone, (s/>n(_,_,_))\<s, lambda(P,quant(forall,X,appl(P,X)))).
lex(before, ((n(A,B,C)\s)\(n(A,B,C)\s))/s, lambda(S,lambda(VP,lambda(NP, appl(appl(before,S),appl(VP,NP)))))).
lex(did, (((n(_,_,_)\s)/>(n(_,_,_)\s))/(n(_,_,_)\s))\((n(_,_,_)\s)/>(n(_,_,_)\s)), lambda(X,lambda(Y,appl(appl(X,Y),Y)))).
lex(that, (cn\cn)/(^(s/<n(_,_,_))), lambda(X,lambda(Y,lambda(Z,bool(appl(X,Z),&,appl(Y,Z)))))).
lex(which, (n(_,_,_)/<n(_,_,_))\<((cn\cn)/(^(s/<n(_,_,_)))), lambda(X,lambda(Y,lambda(Z,lambda(W,bool(appl(Z,W),&,appl(Y,appl(X,W)))))))).
lex(who, (n(A,B,C)\((s/>n(A,B,C))\<s))/(^(s/<n(A,B,C))), lambda(X,lambda(Y,lambda(Z,bool(appl(X,Y),&,appl(Z,Y)))))).
lex(and, ((s/<((n(_,_,_)\s)/n(_,_,_)))\(s/<((n(_,_,_)\s)/n(_,_,_))))/(^(s/<((n(_,_,_)\s)/n(_,_,_)))), lambda(X,lambda(Y,lambda(Z,bool(appl(Y,Z),&,appl(X,Z)))))).
lex(than, cp/s, lambda(X,X)).
lex(more, (s/<d_q)\<(s/(^(cp/<d_q))), lambda(X,lambda(Y,bool(number_of(lambda(Z,appl(X,lambda(P,lambda(Q,bool(appl(P,Z),&,appl(Q,Z))))))),gneq,number_of(lambda(Z1,appl(Y,lambda(P1,lambda(Q1,bool(appl(P1,Z1),&,appl(Q1,Z1))))))))))).
lex(himself, (d_vp(A,B,C)/<n(_,_,_))\<d_vp(A,B,C), lambda(X,lambda(Y,appl(appl(X,Y),Y)))).
lex(himself2, ((d_vp(A,B,C)/>n(D,E,F))/<n(_,_,_))\<(d_vp(A,B,C)/>n(D,E,F)), lambda(X,lambda(Y,appl(appl(X,Y),Y)))).

% = Dutch

lex(dat, cs/s, lambda(X,X)).
lex(jan, n(sg,3,m), j).
lex(henk, n(sg,3,m), h).
lex(cecilia, n(sg,3,f), c).
lex(nijlpaarden, cn, hippos).
lex(de, n(_,_,_)/cn, iota).
lex(boeken, n(pl,3,o), b).
lex(las, n(_,_,_)\(n(_,_,_)\s), read).
lex(kan, (n(A,B,C)\si)\<(n(A,B,C)\s), lambda(VP,lambda(S,appl(appl(can,appl(VP,S)),S)))).
lex(wil, (n(A,B,C)\si)\<(n(A,B,C)\s), lambda(VP,lambda(S,appl(appl(want,appl(VP,S)),S)))).
lex(kunnen, rproj((n(A,B,C)\si)\<(n(A,B,C)\si)), lambda(VP,lambda(S,appl(appl(can,appl(VP,S)),S)))).
lex(lezen, rproj(n(_,_,_)\(n(_,_,_)\si)), read).
lex(voeren, rproj(n(_,_,_)\(n(_,_,_)\si)), feed).
lex(alles, (s/<n(_,_,_))\<s, lambda(X,quant(forall,Y,bool(appl(thing,Y),->,appl(X,Y))))).
lex(alles, (si/<n(_,_,_))\<si, lambda(X,quant(forall,Y,bool(appl(thing,Y),->,appl(X,Y))))).
lex(zag, (n(_,_,_)\si)\<(n(_,_,_)\(n(_,_,_)\s)), lambda(VP,lambda(X,lambda(Y,appl(appl(appl(see,appl(VP,X)),X),Y))))).
lex(helpen, rproj((n(_,_,_)\si)\<(n(_,_,_)\(n(_,_,_)\si))), lambda(VP,lambda(X,lambda(Y,appl(appl(appl(help,appl(VP,X)),X),Y))))).
lex(wil2, q/(^(s/<((n(sg,_,_)\si)\<(n(sg,_,_)\s)))), lambda(P,appl(P,lambda(Q,lambda(X,appl(appl(want,appl(Q,X)),X)))))).
