
test(1) :-
	parse([everyone,loves,someone], s).
test(2) :-
	parse([every,student,read,a,book], s).
test(3) :-
	parse([book,which,every,student,loves], n).


lex(student,  n,                 student,         student).
lex(book,     n,                 book,            book).
lex(read,     (np->np->s),       O^S^(S+read+O),  read).
lex(loves,    (np->np->s),       O^S^(S+loves+O),  loves).
lex(a,        (n->((np->s)->s)), N^P^P@(a+N),     X^Y^quant(exists,Z,bool(X@Z,&,Y@Z))).
lex(every,    (n->((np->s)->s)), N^P^P@(every+N), X^Y^quant(forall,Z,bool(X@Z,->,Y@Z))).
lex(someone,  ((np->s)->s),      P^P@someone,     P^quant(exists,X,bool(person@X,&,P@X))).
lex(everyone, ((np->s)->s),      P^P@everyone,    P^quant(forall,X,bool(person@X,->,P@X))).
lex(which,    ((np->s)->n->n),   P^N^(N+which+P@epsilon), Q^R^X^bool(R@X,&,Q@X)).
lex(and,      (s->s->s),         Q^P^(P+and+Q),   N^M^bool(N,&,M)).
