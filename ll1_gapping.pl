% ====================================
% = First-order linear logic grammar =
% ====================================

% This grammar provides some examples of how to use the first-order variables for some things which cannot directly be implemented
% either in hybrid type-logical grammars or in displacement grammars (even when case is added). The treatment of non-associativity
% and blocking empty antecedent derivations given here is briefly mentioned in Section 6 of the following article
%
% Richard Moot (2014), Extended Lambek calculi and first-order linear logic, in Claudia Casadio, Bob Coecke, Michael Moortgat and
% Philip Scott, eds `Categories and Types in Logic, Language, and Physics: Essays Dedicated to Jim Lambek on the Occasion of His
% 90th Birthday', Springer LNCS 8222, 297-330

:- op(190, yfx, @).

:- abolish(lex/3), abolish(lex/4), abolish(test/1), abolish(atomic_formula/3), abolish(atomic_formula/1), abolish(macro/2).

% For lambda terms, X^M is short for lambda(X,M) and M@N
% is short for appl(M,N). As expected, X^Y^Z^X@Y@Z is
% short for lambda(X,lambda(Y,lambda(Z,appl(appl(X,Y),Z))))
% though be warned that X@Y+V@Z corresponds to (X@Y)+(V@Z)

atomic_formula(up).
atomic_formula(home).
atomic_formula(elect).

% = specify some abbreviations to make the lexical entries slightly more compact

macro(pp(X,Y), at(pp, [X,Y])).
macro(np(X,Y), at(np, [X,Y])).
macro(n(X,Y), at(n, [X,Y])).
macro(s(X,Y), at(s, [X,Y])).
macro(inf(X,Y), at(inf, [X,Y])).
macro(to_inf(X,Y), at(to_inf, [X,Y])).
macro(vp(X,Y), forall(L, impl(np(L,X), s(L,Y)))). 
macro(tv(X,Y), forall(R,impl(at(np, [Y,R]),forall(L,impl(at(np, [L,X]), at(s, [L,R])))))).
% extracted (s/np)/np, with left position L
macro(tvie(L), forall(M,impl(at(np, [L,M]),forall(R,impl(at(np, [M,R]), at(s, [L,R])))))).
macro(tvie_to_inf(L), forall(M,impl(at(np, [L,M]),forall(R,impl(at(np, [M,R]), at(to_inf, [L,R])))))).
macro(tv_to_inf(X,Y), forall(R,impl(at(np, [Y,R]),forall(L,impl(at(np, [L,X]), at(to_inf, [L,R])))))).
macro(tv(A,B,C,D), impl(np(B,C),forall(X,impl(np(X,A), s(X,D))))).
macro(tvi(A,B,C,D), impl(np(B,C),forall(X,impl(np(D,X), s(A,X))))).
%macro(tvi_to_inf(A,B,C,D), impl(np(B,C),forall(X,impl(np(D,X), to_inf(A,X))))).
macro(tvi_to_inf(A,B,C,D), forall(X,forall(Y,impl(impl(np(B,C),to_inf(X,Y)),impl(np(D,X), s(A,Y)))))).
macro(tv_to_inf(A,B,C,D), impl(np(B,C),to_inf(A,D))).
macro(x(Cat1,Cat2,B,C), forall(A, impl(y(Cat1,Cat2,A,B),s(A,C)))).
macro(y(Cat1,Cat2,A,B), forall(C, impl(at(Cat1,[B,C]),forall(D,impl(at(Cat2,[C,D]),s(A,D)))))).

lex(peter, np(L,R), L, R, peter).
lex(suzy, np(L,R), L, R, suzy).
lex(susan, np(L,R), L, R, susan).
lex(john, np(L,R), L, R, john).
lex(jack, np(L,R), L, R, jack).
lex(wilfred, np(L,R), L, R, wilfred).
lex(elsie, np(L,R), L, R, elsie).
lex(phoebe, np(L,R), L, R, phoebe).
lex(wendy, np(L,R), L, R, wendy).
lex(jimmy, np(L,R), L, R, jimmy).
lex(jill, np(L,R), L, R, jill).
lex(time, np(L,R), L, R, time).
lex(newsweek, np(L,R), L, R, newsweek).
lex(agnew, np(L,R), L, R, agnew).
lex(nixon, np(L,R), L, R, nixon).
lex(arizona, np(L,R), L, R, arizona).
lex(goldwater, np(L,R), L, R, goldwater).
lex(pennsylvania, np(L,R), L, R, pennsylvania).
lex(schweiker, np(L,R), L, R, schweiker).

% = particles
lex(home, at(home, [L,R]), L, R, home).
lex(up, at(up, [L,R]), L, R, up).
lex(senator, at(elect, [L,R]), L, R, senator).
lex(president, at(elect, [L,R]), L, R, president).

% = particle verbs
lex(elected, forall(C,forall(D,impl(at(elect, [C,D]), tv(L,R,C,D)))), L, R, elect).
lex(rang, forall(C,forall(D,impl(at(up, [C,D]), tv(L,R,C,D)))), L, R, lambda(_,lambda(Y,lambda(X,appl(appl(ring_up,Y),X))))).
lex(took, forall(C,forall(D,impl(at(home, [C,D]), tv(L,R,C,D)))), L, R, lambda(_,lambda(Y,lambda(X,appl(appl(take_home,Y),X))))).
lex(to_take, forall(C,forall(D,impl(at(home, [C,D]), tv_to_inf(L,R,C,D)))), L, R, lambda(_,lambda(Y,lambda(X,appl(appl(take_home,Y),X))))).

% = to infinitives
lex(to_be_guilty, to_inf(L,R), L, R, guilty).
lex(to_get_married, to_inf(L,R), L, R, get_married).
lex(to_stay, to_inf(L,R), L, R, stay).
lex(to_leave, to_inf(L,R), L, R, leave).

% = infinitives
lex(call, forall(A,impl(np(R,A),inf(L,A))), L, R, call).
lex(greet, forall(A,impl(np(R,A),inf(L,A))), L, R, greet).

% = auxiliaries
lex(should, forall(A,impl(np(R,A),forall(B,impl(inf(A,B),s(L,B))))), L, R, lambda(NP,lambda(INF,appl(should,appl(INF,NP))))).
lex(will, forall(A,impl(np(R,A),forall(B,impl(inf(A,B),s(L,B))))), L, R, lambda(NP,lambda(INF,appl(will,appl(INF,NP))))).
lex(does, forall(A,impl(np(R,A),forall(B,impl(inf(A,B),s(L,B))))), L, R, lambda(NP,lambda(INF,appl(INF,NP)))).

% = control verbs
lex(asked, forall(B,impl(np(R,B),forall(C,impl(to_inf(B,C),forall(A,impl(np(A,L),s(A,C))))))), L, R, lambda(O,lambda(INF,lambda(S,appl(appl(appl(ask,O),appl(INF,O)),S))))).
lex(begged, forall(B,impl(np(R,B),forall(C,impl(to_inf(B,C),forall(A,impl(np(A,L),s(A,C))))))), L, R, lambda(O,lambda(INF,lambda(S,appl(appl(appl(beg,O),appl(INF,O)),S))))).
lex(believes, forall(B,impl(np(R,B),forall(C,impl(to_inf(B,C),forall(A,impl(np(A,L),s(A,C))))))), L, R, lambda(O,lambda(INF,lambda(S,appl(appl(believe,appl(INF,O)),S))))).

% personal pronouns
lex(i, np(L,R), L, R, i).
lex(me, np(L,R), L, R, me).
lex(you, np(L,R), L, R, you).

% adverbs
% the entry below scopes over the left conjunct of a gapping construction only, eg. for sentence 14
lex(first, forall(A,impl(s(A,L),s(A,R))), L, R, first).
% the entry below fails to derive sentence 14 at all
%lex(first, forall(A,impl(inf(A,L),inf(A,R))), L, R, lambda(INF,lambda(X,appl(first,appl(INF,X))))).
lex(rarely, forall(A,impl(s(R,A),s(L,A))), L, R, rarely).
%lex(at_home, forall(A,impl(vp(A,L),vp(A,R))), L, R, at_home).
lex(at_home, forall(A,impl(s(A,L),s(A,R))), L, R, at_home).

% gapping lexical entries
% gapping of (np\s)|np 
lex(and, forall(A,forall(B,forall(C,forall(D,forall(E,forall(F,forall(G,impl(impl(tv(G,G),at(s, [R,F])), impl(impl(tv(A,B,C,D),at(s, [E,L])), impl(tv(A,B,C,D), s(E,F))))))))))), L, R, lambda(P,lambda(Q,lambda(TV,bool(appl(Q,TV),&,appl(P,TV)))))).
lex(or, forall(A,forall(B,forall(C,forall(D,forall(E,forall(F,forall(G,impl(impl(tv(G,G),at(s, [R,F])), impl(impl(tv(A,B,C,D),at(s, [E,L])), impl(tv(A,B,C,D), s(E,F))))))))))), L, R, lambda(P,lambda(Q,lambda(TV,bool(appl(Q,TV),\/,appl(P,TV)))))).
% gapping of (s/np)|np (necessary for sentences 10 and 12)
lex(and, forall(A,forall(B,forall(C,forall(D,forall(E,forall(F,forall(G,impl(impl(tvie(G),s(R,F)), impl(impl(tvi(A,B,C,D),s(E,L)), impl(tvi(A,B,C,D), s(E,F))))))))))), L, R, lambda(P,lambda(Q,lambda(TV,bool(appl(Q,TV),&,appl(P,TV)))))).
lex(or,  forall(A,forall(B,forall(C,forall(D,forall(E,forall(F,forall(G,impl(impl(tvie(G),s(R,F)), impl(impl(tvi(A,B,C,D),s(E,L)), impl(tvi(A,B,C,D), s(E,F))))))))))), L, R, lambda(P,lambda(Q,lambda(TV,bool(appl(Q,TV),\/,appl(P,TV)))))).
%
%lex(and, forall(A,forall(B,forall(C,forall(D,forall(E,forall(F,forall(G,impl(impl(forall(H,tvi_to_inf(G,H,H,G)),s(R,F)), impl(impl(tvi_to_inf(A,B,C,D),s(E,L)), impl(tvi_to_inf(A,B,C,D), s(E,F))))))))))), L, R, lambda(P,lambda(Q,lambda(TV,bool(appl(Q,TV),&,appl(P,TV)))))).

% argument cluster coordination for np and to_inf
% (X\X)/X for X = ((s/to_inf)/np)\s
%lex(and, forall(G, impl(x(np,to_inf,R,G),forall(A,impl(x(np,to_inf,A,L),x(np,to_inf,A,G))))), L, R, lambda(P2,lambda(P1,lambda(Q,bool(appl(P2,Q),&,appl(P1,Q)))))).
% argument cluster coordination for two np's (this entry simply serves as a control against overgeneration)
%lex(and, forall(G, impl(x(np,np,R,G),forall(A,impl(x(np,np,A,L),x(np,np,A,G))))), L, R, lambda(P2,lambda(P1,lambda(Q,bool(appl(P2,Q),&,appl(P1,Q)))))).
% is this entry useful?
%lex(and, forall(A,forall(B,forall(C,forall(D,forall(E,forall(F,forall(G,impl(impl(tvie_to_inf(G),s(R,F)), impl(impl(tvi_to_inf(A,B,C,D),s(E,L)), impl(tvi_to_inf(A,B,C,D), s(E,F))))))))))), L, R, lambda(P,lambda(Q,lambda(TV,bool(appl(Q,TV),&,appl(P,TV)))))).

% = discontinuous gapping
test(1) :-
	parse([peter,rang,suzy,up], s).
test(2) :-
	parse([peter,rang,suzy,up,and,john,wendy], s).
test(3) :-
	parse([peter,took,suzy,home], s).
test(4) :-
	parse([peter,took,suzy,home,and,john,wendy], s).
test(5) :-
	parse([time,believes,agnew,to_be_guilty], s).
% Sag (1976), p. 274
test(6) :-
	parse([time,believes,agnew,to_be_guilty,and,newsweek,nixon], s).
test(7) :-
	parse([arizona,elected,goldwater,senator], s).
% Jackendoff (1971), p. 24
test(8) :-
	parse([arizona,elected,goldwater,senator,and,pennsylvania,schweiker], s).
%
test(9) :-
	parse([jack,begged,elsie,to_get_married], s).
% Jackendoff (1971), p. 24
test(10) :-
	parse([jack,begged,elsie,to_get_married,and,wilfred,phoebe], s).
test(11) :-
	parse([should,i,call,you], s).
%
test(12) :-
	parse([should,i,call,you,or,you,me], s).
test(13) :-
	parse([will,jimmy,greet,jill,first], s).
% succeeds with incorrect scope of "first"
test(14) :-
	parse([will,jimmy,greet,jill,first,or,jill,jimmy], s).
test(15) :-
	parse([i,asked,peter,to_take,susan,home], s).
% two readings, both using the (np\s)|np assignment; is it possible to get the third using the (s/np)|np assignment?
% v 1) I asked Peter to take Susan home and           John [asked Peter to take] Wendy [home]
% v 2) I asked Peter to take Susan home and           John [asked]               Wendy [to take Susan home]
% x 3) I asked Peter to take Susan home and [I asked] John [to take]             Wendy [home]
test(16) :-
	parse([i,asked,peter,to_take,susan,home,and,john,wendy], s).
test(17) :-
	parse([i,asked,peter,to_leave], s).
test(18) :-
	parse([i,asked,peter,to_leave,and,susan,to_stay], s).
% this is the "unreduced form" of reading 3 of sentence 16
test(19) :-
	parse([i,asked,peter,to_take,susan,home,and,john,to_take,wendy,home], s).
test(20) :-
	parse([rarely,does,john,call,mary], s).
test(21) :-
	parse([rarely,does,john,call,mary,and,mary,john], s).
% closest is at_home(rarely(...) & rarely(...), I believe the correct reading should rather be
% rarely(at_home(...)) & rarely(at_home(...)) though only the left conjunct is currently generated
% in this form
test(22) :-
	parse([rarely,does,john,call,mary,at_home,and,mary,john], s).
