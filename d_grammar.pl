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

:- abolish(lex/3), abolish(lex/4), abolish(test/1).

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
	parse([mountain,the,painting,of,which,by,cezanne,john,sold,for,ten_million_dollars], cn).
test(8) :-
	parse([john,who,jogs,sneezed], s).
test(9) :-
	parse([john,studies,logic,and,charles,phonetics], s).
test(10) :-
	parse([john,ate,more,donuts,than,mary,bought,bagels], s).
test(11) :-
	parse([dat,jan,boeken,las], cs).
test(12) :-
	parse([dat,jan,boeken,kan,lezen], cs).
test(13) :-
	parse([dat,jan,boeken,wil,kunnen,lezen], cs).
test(14) :-
	parse([dat,jan,alles,las], cs).
test(15) :-
	parse([dat,jan,alles,kan,lezen], cs).
test(16) :-
	parse([dat,jan,cecilia,de,nijlpaarden,zag,voeren], cs).
test(17) :-
	parse([dat,jan,cecilia,henk,de,nijlpaarden,zag,helpen,voeren], cs).
test(18) :-
	parse([wil2,jan,boeken,lezen], q).
test(19) :-
	parse([jan,wil2,boeken,lezen], n*(^(q/<n))).
test(20) :-
	parse([john,bought,himself,coffee], s).
test(21) :-
	parse([every,man,loves,himself], s).
test(22) :-
	parse([mary,talked,to,john,about,himself2], s).
test(23) :-
	parse([mary,talked,about,himself2,to,john], s).

lex(john, n, j).
lex(mary, n, m).
lex(charles, n, c).
lex(logic, n, l).
lex(phonetics, n, p).
lex(cezanne, n, cezanne).
lex(coffee, n, coffee).
lex(the, n/cn, iota).
lex(ten_million_dollars, n, '\\$10.000.000').
lex(thinks, (n\s)/s, think).
lex(left, n\s, leave).
lex(slept, n\s, sleep).
lex(jogs, n\s, jog).
lex(sneezed, n\s, sneeze).
lex(loves, (n\s)/n, love).
lex(saw, (n\s)/n, see).
lex(studies, (n\s)/n, study).
lex(ate, d_tv, eat).
lex(bought, d_tv, buy).
lex(bought, (d_tv)/n, buy).
lex(talked, ((n\s)/pp)/pp, talk).
lex(today, (n\s)\(n\s), lambda(VP,lambda(N,appl(today,appl(VP,N))))).
lex(gave, (n\s)/(n*pp), lambda(Pair,lambda(X,appl(appl(appl(g,pi2(Pair)),pi1(Pair)),X)))).
lex(gave, lproj(((n\s)/<n)/tcs), lambda(_TCS,shun)).
lex(the_cold_shoulder, tcs, tcs).
lex(gave2, ((n\s)/pp)/n, give).
lex(sold, ((n\s)/pp)/n, 'sell\\_for').
lex(book, cn, b).
lex(dog, cn, dog).
lex(man, cn, man).
lex(donuts, cn, donuts).
lex(bagels, cn, bagels).
lex(mountain, cn, mountain).
lex(painting, cn/pp, 'painting\\_of').
lex(of, pp/n, lambda(X,X)).
lex(by, (cn\cn)/n, by).
lex(for, pp/n, lambda(X,X)).
lex(to, pp/n, lambda(X,X)).
lex(about, pp/n, lambda(X,X)).
lex(every, d_q, lambda(X,lambda(Y,quant(forall,Z,bool(appl(X,Z),->,appl(Y,Z)))))).
lex(someone, (s/>n)\<s, lambda(P,quant(exists,X,appl(P,X)))).
lex(everyone, (s/>n)\<s, lambda(P,quant(forall,X,appl(P,X)))).
lex(before, ((n\s)\(n\s))/s, lambda(S,lambda(VP,lambda(NP, appl(appl(before,S),appl(VP,NP)))))).
lex(did, (((n\s)/>(n\s))/(n\s))\((n\s)/>(n\s)), lambda(X,lambda(Y,appl(appl(X,Y),Y)))).
lex(that, (cn\cn)/(^(s/<n)), lambda(X,lambda(Y,lambda(Z,bool(appl(X,Z),&,appl(Y,Z)))))).
lex(which, (n/<n)\<((cn\cn)/(^(s/<n))), lambda(X,lambda(Y,lambda(Z,lambda(W,bool(appl(Z,W),&,appl(Y,appl(X,W)))))))).
lex(who, (n\((s/>n)\<s))/(^(s/<n)), lambda(X,lambda(Y,lambda(Z,bool(appl(X,Y),&,appl(Z,Y)))))).
lex(and, ((s/<((n\s)/n))\(s/<((n\s)/n)))/(^(s/<((n\s)/n))), lambda(X,lambda(Y,lambda(Z,bool(appl(Y,Z),&,appl(X,Z)))))).
lex(than, cp/s, lambda(X,X)).
lex(more, (s/<d_q)\<(s/(^(cp/<d_q))), lambda(X,lambda(Y,bool(number_of(lambda(Z,appl(X,lambda(P,lambda(Q,bool(appl(P,Z),&,appl(Q,Z))))))),gneq,number_of(lambda(Z1,appl(Y,lambda(P1,lambda(Q1,bool(appl(P1,Z1),&,appl(Q1,Z1))))))))))).
lex(himself, (d_vp/<n)\<d_vp, lambda(X,lambda(Y,appl(appl(X,Y),Y)))).
lex(himself2, ((d_vp/<n)/<n)\<(d_vp/<n), lambda(X,lambda(Y,appl(appl(X,Y),Y)))).

% = Dutch

lex(dat, cs/s, lambda(X,X)).
lex(jan, n, j).
lex(henk, n, h).
lex(cecilia, n, c).
lex(nijlpaarden, cn, hippos).
lex(de, n/cn, iota).
lex(boeken, n, b).
lex(las, n\(n\s), read).
lex(kan, (n\si)\<(n\s), lambda(VP,lambda(S,appl(appl(can,appl(VP,S)),S)))).
lex(wil, (n\si)\<(n\s), lambda(VP,lambda(S,appl(appl(want,appl(VP,S)),S)))).
lex(kunnen, rproj((n\si)\<(n\si)), lambda(VP,lambda(S,appl(appl(can,appl(VP,S)),S)))).
lex(lezen, rproj(n\(n\si)), read).
lex(voeren, rproj(n\(n\si)), feed).
lex(alles, (s/<n)\<s, lambda(X,quant(forall,Y,bool(appl(thing,Y),->,appl(X,Y))))).
lex(alles, (si/<n)\<si, lambda(X,quant(forall,Y,bool(appl(thing,Y),->,appl(X,Y))))).
lex(zag, (n\si)\<(n\(n\s)), lambda(VP,lambda(X,lambda(Y,appl(appl(appl(see,appl(VP,X)),X),Y))))).
lex(helpen, rproj((n\si)\<(n\(n\si))), lambda(VP,lambda(X,lambda(Y,appl(appl(appl(help,appl(VP,X)),X),Y))))).
lex(wil2, q/(^(s/<((n\si)\<(n\s)))), lambda(P,appl(P,lambda(Q,lambda(X,appl(appl(want,appl(Q,X)),X)))))).
