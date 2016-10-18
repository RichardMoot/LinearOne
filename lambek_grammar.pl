% =================================
% =        Lambek grammar         =
% =================================
%
% However, we do have the familiar a/b/c = (a/b)/c and
% c\b\a = (c\(b\a) and even a\b/c = (a\b)/c.
%
% For lambda terms, X^M is short for lambda(X,M) and M@N
% is short for appl(M,N). As expected, X^Y^Z^X@Y@Z is
% short for lambda(X,lambda(Y,lambda(Z,appl(appl(X,Y),Z))))
% though be warned that X@Y+V@Z corresponds to (X@Y)+(V@Z)

:- op(400, xfy, \).
:- op(190, yfx, @).

:- abolish(lex/3), abolish(lex/4), abolish(test/1), abolish(atomic_formula/3), abolish(atomic_formula/1), abolish(macro/2).

lex(every, (s/(np\s))/n, lambda(P,lambda(Q,quant(forall,X,bool(appl(P,X),->,appl(Q,X)))))).
lex(some, ((s/np)\s)/n, lambda(P,lambda(Q,quant(exists,X,bool(appl(P,X),&,appl(Q,X)))))).
lex(student, n, student).
lex(exam, n, exam).
lex(aced, (np\s)/np, ace).
lex(slept, np\s, sleep).
lex(during, ((np\s)\(np\s))/np, lambda(X,lambda(P,lambda(Y,appl(appl(during,X),appl(P,Y)))))).
lex(the, np/n, iota).
lex(who, (n\n)/(np\s), lambda(P,lambda(Q,lambda(X,bool(appl(Q,X),&,appl(P,X)))))).
lex(loves, (np\s)/np, love).
lex(alyssa, np, alyssa).

test(1) :-
	parse([every,student,aced,some,exam], s).

test(2) :-
	parse([the,student,who,slept,during,the,exam,loves,alyssa], s).
