% define operators to allow for easier specification of
% displacement calculus lexical entries.
%
% WARNING: in case of doubt, use parentheses to disambiguate!
% I have deliberately not changed the definitions of standard
% mathematical and logical operations of Prolog, notably |
% (alternative of ; for use in DCG), \ and *.
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
:- op(400, xfy, \).

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
	/* check proof generation */
	parse([dog,that,mary,saw,today], cn).
test(7) :-
	/* ??? check this */
	parse([mountain,the,painting,of,which,by,cezanne,john,sold,for,ten_million_dollars], cn).
test(8) :-
	parse([john,who,jogs,sneezed], s).
test(9) :-
	parse([john,studies,logic,and,charles,phonetics], s).

lex(john, n, j).
lex(mary, n, m).
lex(charles, n, c).
lex(logic, n, l).
lex(phonetics, n, p).
lex(cezanne, n, cezanne).
lex(the, cn/n, '\\iota').
lex(ten_million_dollars, n, '\\$10.000.000').
lex(thinks, (n\s)/s, think).
lex(left, n\s, leave).
lex(slept, n\s, sleep).
lex(jogs, n\s, jog).
lex(sneezed, n\s, sneeze).
lex(loves, (n\s)/n, love).
lex(saw, (n\s)/n, see).
lex(studies, (n\s)/n, study).
lex(today, (n\s)\(n\s), lambda(VP,lambda(N,appl(today,appl(VP,N))))).
lex(gave, (n\s)/(n*pp), lambda(Pair,lambda(X,appl(appl(appl(g,pi2(Pair)),pi1(Pair)),X)))).
lex(gave, lproj(((n\s)/<n)/tcs), lambda(_TCS,shun)).
lex(the_cold_shoulder, tcs, tcs).
lex(gave2, ((n\s)/pp)/n, give).
lex(sold, ((n\s)/pp)/n, sell).
lex(book, cn, b).
lex(dog, cn, dog).
lex(mountain, cn, mountain).
lex(painting, cn/pp, painting).
lex(of, pp/n, lambda(X,X)).
lex(by, (cn\cn)/n, by).
lex(for, pp/n, lambda(X,X)).
lex(to, pp/n, lambda(X,X)).
lex(every, ((s/>n)\<s)/cn, lambda(X,lambda(Y,quant(forall,Z,bool(appl(X,Y),->,appl(Y,Z)))))).
lex(someone, (s/>n)\<s, lambda(P,quant(exists,X,appl(P,X)))).
lex(everyone, (s/>n)\<s, lambda(P,quant(forall,X,appl(P,X)))).
lex(before, ((n\s)\(n\s))/s, lambda(S,lambda(VP,lambda(NP, appl(appl(before,S),appl(VP,NP)))))).
lex(did, (((n\s)/>(n\s))/(n\s))\((n\s)/>(n\s)), lambda(X,lambda(Y,appl(appl(X,Y),Y)))).
lex(that, (cn\cn)/(^(s/<n)), lambda(X,lambda(Y,lambda(Z,bool(appl(X,Z),&,appl(Y,Z)))))).
lex(which, (n/<n)\<((cn\cn)/(^(s/<n))), lambda(X,lambda(Y,lambda(Z,lambda(W,bool(appl(Z,W),&,appl(Y,appl(X,W)))))))).
lex(who, (n\((s/>n)\<s))/(^(s/<n)), lambda(X,lambda(Y,lambda(Z,bool(appl(X,Y),&,appl(Z,Y)))))).
lex(and, ((s/<((n\s)/n))\(s/<((n\s)/n)))/(^(s/<(n\s)/n)), lambda(X,lambda(Y,lambda(Z,bool(appl(Y,Z),&,appl(X,Z)))))).
