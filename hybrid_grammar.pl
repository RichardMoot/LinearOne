:- op(400, xfy, \).

test(1) :-
	parse([someone,talked,to,everyone,yesterday], s).
test(2) :-
	parse([leslie,bought,a,cd,and,robin,a,book], s).
test(3) :-
	parse([robin,must,discover,a,solution], s).
test(4) :-
	parse([john,cant,eat,steak,and,mary,pizza], s).
% split scope
test(5) :-
	parse([no2,neg,fish,walks], s).
test(6) :-
	parse([no2,neg,dog,eats,whiskas,or2,neg,cat,alpo], s).
% comparative subdeletion
test(7) :-
	parse([john,ate,more,donuts,than,mary,bought,bagels], s).
test(8) :-
	parse([no,fish,walks], s).
% NOTE: The next two examples make the need for a better atom selection strategy evident!
test(9) :-
	/* 3,142,516 axioms ! */
        /* 5,808,425,093 inferences, 2014.396 CPU in 2139.522 seconds (94% CPU, 2883458 Lips) */
	parse([no,dog,eats,whiskas,or,cat,alpo], s).
test(10) :-
	parse([no,dog,eats,more,whiskas2,than,leslie,buys,donuts,or,cat,alpo2], s).

lex(leslie, np, leslie, l).
lex(robin, np, robin, r).
lex(john, np, john, j).
lex(mary, np, mary, m).
lex(bought, tv, bought, buy).
lex(buys, tv, buys, buy).
lex(eats, tv, eats, eat).
lex(ate, tv, ate, eat).
lex(talked, (np\s)/pp, talked, talk).
lex(discover, tv, discover, discover).
lex(walks, np\s, walks, walk).
lex(eat, tv, eat, eat).
lex(a, ((s|(s|np))|n), lambda(N,lambda(P,lambda(Z,appl(appl(P,lambda(V,appl(a,appl(N,V)))),Z)))), lambda(X,lambda(Y,quant(exists,Z,bool(appl(X,Z),&,appl(Y,Z)))))).
lex(someone, (s|(s|np)), lambda(P,lambda(Z,appl(appl(P,someone),Z))), lambda(P,quant(exists,X,bool(appl(person,X),&,appl(P,X))))).
lex(everyone, (s|(s|np)), lambda(P,lambda(Z,appl(appl(P,everyone),Z))), lambda(P,quant(forall,X,bool(appl(person,X),->,appl(P,X))))).
lex(yesterday, (np\s)\(np\s), yesterday, lambda(X,lambda(Y,appl(yesterday,appl(X,Y))))).
lex(fish, n, fish, fish).
lex(dog, n, dog, dog).
lex(cat, n, cat, cat).
lex(cd, n, cd, cd).
lex(book, n, book, book).
lex(donuts, n, donuts, donuts).
lex(bagels, n, bagels, bagels).
lex(solution, n, solution, solution).
lex(steak, np, steak, steak).
lex(pizza, np, pizza, pizza).
lex(whiskas, np, whiskas, whiskas).
lex(alpo, np, alpo, alpo).
lex(whiskas2, n, whiskas2, whiskas).
lex(alpo2, n, alpo2, alpo).
lex(to, pp/np, to, lambda(X,X)).
lex(and, (((s|tv)|(s|tv))|(s|tv)), lambda(STV2,lambda(STV1,lambda(TV,lambda(V,appl(appl(STV1,TV),appl(and,appl(appl(STV2,lambda(W,W)),V))))))), lambda(S2,lambda(S1,lambda(T,bool(appl(S1,T),&,appl(S2,T)))))).
lex(must, (s|(s|(vp/vp))), lambda(SVP,lambda(Z,appl(appl(SVP,must),Z))), lambda(F,necessary(appl(F,lambda(Y,Y))))).
lex(cant, (s|(s|(vp/vp))), lambda(SVP,lambda(Z,appl(appl(SVP,cant),Z))), lambda(F,neg(possible(appl(F,lambda(Y,Y)))))).
lex(no, (s|(s|h_det)), lambda(Rho,lambda(Z,appl(appl(Rho,lambda(Phi,lambda(Sigma,lambda(V,appl(appl(Sigma,lambda(W,appl(no,appl(Phi,W)))),V))))),Z))), lambda(P,neg(appl(P,lambda(Q,lambda(R,quant(exists,X,bool(appl(Q,X),&,appl(R,X))))))))).
lex(than, than, than, lambda(X,X)).
lex(more, (((s|(s|h_det))|(s|h_det))|than), lambda(Than,lambda(Rho1,lambda(Rho2,lambda(Z,appl(appl(Rho2,lambda(Phi,lambda(Sigma,appl(Sigma,lambda(V,appl(more,appl(Phi,V))))))),appl(Than,appl(appl(Rho1,lambda(Phi2,lambda(Sigma2,lambda(W,appl(appl(Sigma2,Phi2),W))))),Z))))))), lambda(_,lambda(F,lambda(G,bool(number_of(appl(G,lambda(P,lambda(Q,lambda(X,bool(appl(P,X),&,appl(Q,X))))))),gneq,number_of(appl(F,lambda(P2,lambda(Q2,lambda(Y,bool(appl(P2,Y),&,appl(Q2,Y)))))))))))).
lex(or, ((((s|h_det)|tv)|((s|h_det)|tv))|((s|h_det)|tv)), lambda(Rho2,lambda(Rho1,lambda(Phi,lambda(Tau,lambda(Z,appl(appl(appl(Rho1,Phi),Tau),appl(or,appl(appl(appl(Rho2,lambda(V,V)),lambda(Phi2,lambda(Sigma2,lambda(W,appl(appl(Sigma2,Phi2),W))))),Z)))))))), lambda(SDTV2,lambda(SDTV1,lambda(TV,lambda(Det,bool(appl(appl(SDTV1,TV),Det),\/,appl(appl(SDTV2,TV),Det))))))).

% lexical entries for "split scope"

lex(no2, (s|sneg), lambda(S,lambda(Z,appl(appl(S,no2),Z))), neg).
lex(or2, (((sneg|tv)|(sneg|tv))|(sneg|tv)), lambda(Sigma2,lambda(Sigma1,lambda(Phi1,lambda(Phi2,lambda(Z,appl(appl(appl(Sigma1,Phi1),Phi2),appl(or2,appl(appl(appl(Sigma2,lambda(V,V)),lambda(W,W)),Z)))))))), lambda(V,lambda(W,lambda(TV,bool(appl(W,TV),\/,appl(V,TV)))))).
lex(neg, ((sneg|(s|np))|n), lambda(Phi1,lambda(Sigma,lambda(Phi2,lambda(Z,appl(appl(Sigma,lambda(V,appl(Phi2,appl(neg,appl(Phi1,V))))),Z))))), lambda(X,lambda(Y,quant(exists,Z,bool(appl(X,Z),&,appl(Y,Z)))))).
