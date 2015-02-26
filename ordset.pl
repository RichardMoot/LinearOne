% -*- Mode: Prolog -*-
% This is the file ordset.pl from the Public Domain DEC-10 Prolog
% Library. The only changes and additions to the code are the
% following. They are marked as such in the source code. 20030605 RM
%
% Replaced ord_union with an improved, pure version, also due to
% R.A.O'Keefe.                                                    RM
%
% Added an ord_member predicate, which functions like member_chk for
% lists, using the order of the elements.                         RM
%
% Added an ord_select predicate, which is deterministic when we know
% the element to be selected.                                     RM
%
% Added an ord_dup_insert predicate, which is exactly like ord_insert
% except for the fact that the result is an ordered multiset instead
% of an ordered set                                               RM

%   File   : ORDSET.PL
%   Author : R.A.O'Keefe
%   Updated: 22 May 1983
%   Purpose: Ordered set manipulation utilities

%   In this module, sets are represented by ordered lists with no
%   duplicates.  Thus {c,r,a,f,t} would be [a,c,f,r,t].  The ordering
%   is defined by the @< family of term comparison predicates, which
%   is the ordering used by sort/2 and setof/3.

%   The benefit of the ordered representation is that the elementary
%   set operations can be done in time proportional to the Sum of the
%   argument sizes rather than their Product.  Some of the unordered
%   set routines, such as member/2, length/2,, select/3 can be used
%   unchanged.  The main difficulty with the ordered representation is
%   remembering to use it!

:- module(ordset, [
	list_to_ord_set/2,	%  List -> Set
	ord_merge/3,		%  OrdList x OrdList -> OrdList
	ord_disjoint/2,		%  Set x Set ->
	ord_insert/3,		%  Set x Elem -> Set
	ord_intersect/2,	%  Set x Set ->
	ord_intersect/3,	%  Set x Set -> Set
	ord_seteq/2,		%  Set x Set ->
	ord_subset/2,		%  Set x Set ->
	ord_subtract/3,		%  Set x Set -> Set
	ord_symdiff/3,		%  Set x Set -> Set
	ord_union/3,            %  Set x Set -> Set
	ord_key_intersect/3,    %  Set x Set -> Set
	ord_key_union/3,        %  Set x Set -> Set
	ord_key_union_i/3,      %  Set x Set -> Set
	ord_key_select/4,       %  Key x Set -> Value x Set
	ord_key_delete/3,       %  Set x Key -> Set
        ord_key_insert/4, %  Set x Key x Value -> Set
	ord_member/2,           %  Elem x Set ->
	ord_key_member/3,       %  Key x Set -> Value
	ord_dup_insert/3,       %  Set x Elem -> Set
	ord_delete/3,           %  Set x Elem -> Set
	ord_select/3] ).	%  Elem x Set -> Set

%   list_to_ord_set(+List, ?Set)
%   is true when Set is the ordered representation of the set represented
%   by the unordered representation List.  The only reason for giving it
%   a name at all is that you may not have realised that sort/2 could be
%   used this way.

list_to_ord_set(List, Set) :-
	sort(List, Set).


%   ord_merge(+List1, +List2, -Merged)
%   is true when Merged is the stable merge of the two given lists.
%   If the two lists are not ordered, the merge doesn't mean a great
%   deal.  Merging is perfectly well defined when the inputs contain
%   duplicates, and all copies of an element are preserved in the
%   output, e.g. merge("122357", "34568", "12233455678").  Study this
%   routine carefully, as it is the basis for all the rest.

ord_merge([Head1|Tail1], [Head2|Tail2], [Head2|Merged]) :-
	Head1 @> Head2, !,
	ord_merge([Head1|Tail1], Tail2, Merged).
ord_merge([Head1|Tail1], List2, [Head1|Merged]) :-
	List2 \== [], !,
	ord_merge(Tail1, List2, Merged).
ord_merge([], List2, List2) :- !.
ord_merge(List1, [], List1).



%   ord_disjoint(+Set1, +Set2)
%   is true when the two ordered sets have no element in common.  If the
%   arguments are not ordered, I have no idea what happens.

ord_disjoint([], _) :- !.
ord_disjoint(_, []) :- !.
ord_disjoint([Head1|Tail1], [Head2|Tail2]) :-
	compare(Order, Head1, Head2),
	ord_disjoint(Order, Head1, Tail1, Head2, Tail2).

ord_disjoint(<, _, Tail1, Head2, Tail2) :-
	ord_disjoint(Tail1, [Head2|Tail2]).
ord_disjoint(>, Head1, Tail1, _, Tail2) :-
	ord_disjoint([Head1|Tail1], Tail2).


%   ord_insert(+Set1, +Element, ?Set2)
%   is the equivalent of add_element for ordered sets.  It should give
%   exactly the same result as merge(Set1, [Element], Set2), but a bit
%   faster, and certainly more clearly.

ord_insert([], Element, [Element]).
ord_insert([Head|Tail], Element, Set) :-
	compare(Order, Head, Element),
	ord_insert(Order, Head, Tail, Element, Set).


ord_insert(<, Head, Tail, Element, [Head|Set]) :-
	ord_insert(Tail, Element, Set).
ord_insert(=, Head, Tail, _, [Head|Tail]).
ord_insert(>, Head, Tail, Element, [Element,Head|Tail]).



%   ord_intersect(+Set1, +Set2)
%   is true when the two ordered sets have at least one element in common.
%   Note that the test is == rather than = .

ord_intersect([Head1|Tail1], [Head2|Tail2]) :-
	compare(Order, Head1, Head2),
	ord_intersect(Order, Head1, Tail1, Head2, Tail2).

ord_intersect(=, _, _, _, _).
ord_intersect(<, _, Tail1, Head2, Tail2) :-
	ord_intersect(Tail1, [Head2|Tail2]).
ord_intersect(>, Head1, Tail1, _, Tail2) :-
	ord_intersect([Head1|Tail1], Tail2).



%   ord_intersect(+Set1, +Set2, ?Intersection)
%   is true when Intersection is the ordered representation of Set1
%   and Set2, provided that Set1 and Set2 are ordered sets.

%   modified to work without cuts, like ord_union/3     20040429 RM
%   removed error in the base case                      20040503 RM

ord_intersect([], _, []).
ord_intersect([H1|T1], Set2, Intersection) :-
	ord_intersect_2(Set2, H1, T1, Intersection).

ord_intersect_2([], _, _, []).
ord_intersect_2([H2|T2], H1, T1, Intersection) :-
	compare(Order, H1, H2),
	ord_intersect_3(Order, H1, T1, H2, T2, Intersection).

ord_intersect_3(<, _, T1, H2, T2, Intersection) :-
	ord_intersect_2(T1, H2, T2, Intersection).
ord_intersect_3(=, H1, T1, _, T2, [H1|Intersection]) :-
	ord_intersect(T1, T2, Intersection).
ord_intersect_3(>, H1, T1, _, T2, Intersection) :-
	ord_intersect_2(T2, H1, T1, Intersection).

/* original code

ord_intersect(_, [], []) :- !.
ord_intersect([], _, []) :- !.
ord_intersect([Head1|Tail1], [Head2|Tail2], Intersection) :-
	compare(Order, Head1, Head2),
	ord_intersect(Order, Head1, Tail1, Head2, Tail2, Intersection).

ord_intersect(=, Head,  Tail1, _,     Tail2, [Head|Intersection]) :-
	ord_intersect(Tail1, Tail2, Intersection).
ord_intersect(<, _,     Tail1, Head2, Tail2, Intersection) :-
	ord_intersect(Tail1, [Head2|Tail2], Intersection).
ord_intersect(>, Head1, Tail1, _,     Tail2, Intersection) :-
	ord_intersect([Head1|Tail1], Tail2, Intersection).

*/

%   ord_seteq(+Set1, +Set2)
%   is true when the two arguments represent the same set.  Since they
%   are assumed to be ordered representations, they must be identical.


ord_seteq(Set1, Set2) :-
	Set1 == Set2.



%   ord_subset(+Set1, +Set2)
%   is true when every element of the ordered set Set1 appears in the
%   ordered set Set2.

ord_subset([], _) :- !.
ord_subset([Head1|Tail1], [Head2|Tail2]) :-
	compare(Order, Head1, Head2),
	ord_subset(Order, Head1, Tail1, Head2, Tail2).

ord_subset(=, _, Tail1, _, Tail2) :-
	ord_subset(Tail1, Tail2).
ord_subset(>, Head1, Tail1, _, Tail2) :-
	ord_subset([Head1|Tail1], Tail2).



%   ord_subtract(+Set1, +Set2, ?Difference)
%   is true when Difference contains all and only the elements of Set1
%   which are not also in Set2.


ord_subtract(Set1, [], Set1) :- !.
ord_subtract([], _, []) :- !.
ord_subtract([Head1|Tail1], [Head2|Tail2], Difference) :-
	compare(Order, Head1, Head2),
	ord_subtract(Order, Head1, Tail1, Head2, Tail2, Difference).

ord_subtract(=, _,     Tail1, _,     Tail2, Difference) :-
	ord_subtract(Tail1, Tail2, Difference).
ord_subtract(<, Head1, Tail1, Head2, Tail2, [Head1|Difference]) :-
	ord_subtract(Tail1, [Head2|Tail2], Difference).
ord_subtract(>, Head1, Tail1, _,     Tail2, Difference) :-
	ord_subtract([Head1|Tail1], Tail2, Difference).



%   ord_symdiff(+Set1, +Set2, ?Difference)
%   is true when Difference is the symmetric difference of Set1 and Set2.

ord_symdiff(Set1, [], Set1) :- !.
ord_symdiff([], Set2, Set2) :- !.
ord_symdiff([Head1|Tail1], [Head2|Tail2], Difference) :-
	compare(Order, Head1, Head2),
	ord_symdiff(Order, Head1, Tail1, Head2, Tail2, Difference).

ord_symdiff(=, _,     Tail1, _,     Tail2, Difference) :-
	ord_symdiff(Tail1, Tail2, Difference).
ord_symdiff(<, Head1, Tail1, Head2, Tail2, [Head1|Difference]) :-
	ord_symdiff(Tail1, [Head2|Tail2], Difference).
ord_symdiff(>, Head1, Tail1, Head2, Tail2, [Head2|Difference]) :-
	ord_symdiff([Head1|Tail1], Tail2, Difference).



%   ord_union(+Set1, +Set2, ?Union)
%   is true when Union is the union of Set1 and Set2.  Note that when
%   something occurs in both sets, we want to retain only one copy.

%   replaced original code with improved code from Richard A. O'Keefe's
%   `The Craft of Prolog' (1990) MIT Press. Read this book for discussion
%   and comments on the code.                                          RM

ord_union([], Set2, Set2).
ord_union([H1|T1], Set2, Union) :-
	ord_union_2(Set2, H1, T1, Union).

ord_union_2([], H1, T1, [H1|T1]).
ord_union_2([H2|T2], H1, T1, Union) :-
	compare(Order, H1, H2),
	ord_union_3(Order, H1, T1, H2, T2, Union).

ord_union_3(<, H1, T1, H2, T2, [H1|Union]) :-
	ord_union_2(T1, H2, T2, Union).
ord_union_3(=, H1, T1, _, T2, [H1|Union]) :-
	ord_union(T1, T2, Union).
ord_union_3(>, H1, T1, H2, T2, [H2|Union]) :-
	ord_union_2(T2, H1, T1, Union).

/* original code

ord_union(Set1, [], Set1) :- !.
ord_union([], Set2, Set2) :- !.
ord_union([Head1|Tail1], [Head2|Tail2], Union) :-
	compare(Order, Head1, Head2),
	ord_union(Order, Head1, Tail1, Head2, Tail2, Union).

ord_union(=, Head,  Tail1, _,     Tail2, [Head|Union]) :-
	ord_union(Tail1, Tail2, Union).
ord_union(<, Head1, Tail1, Head2, Tail2, [Head1|Union]) :-
	ord_union(Tail1, [Head2|Tail2], Union).
ord_union(>, Head1, Tail1, Head2, Tail2, [Head2|Union]) :-
	ord_union([Head1|Tail1], Tail2, Union).
*/

%   ord_dup_insert(+Set1, +Element, ?Set2)
%
% implementation of ord_insert for ordered *multisets*              RM

ord_dup_insert([], Element, [Element]).
ord_dup_insert([Head|Tail], Element, Set) :-
	compare(Order, Head, Element),
	ord_dup_insert(Order, Head, Tail, Element, Set).


ord_dup_insert(<, Head, Tail, Element, [Head|Set]) :-
	ord_dup_insert(Tail, Element, Set).
ord_dup_insert(=, Head, Tail, Element, [Element,Head|Tail]).
ord_dup_insert(>, Head, Tail, Element, [Element,Head|Tail]).

% = ord_member(+Element, +OrdSet)
%
% given that the OrdSet is ordered, if we know Element, we can use the
% order to get this element deterministically.                      RM

ord_member(Element, [Head|Tail]) :-
	compare(Order, Element, Head),
	ord_member(Order, Element, Tail).

ord_member(=, _, _).
ord_member(>, Element, Tail) :-
	ord_member(Element, Tail).

% = ord_select(+Element, +OrdSet, ?OrdSet)
%
% given that the OrdSet is ordered, if we know Element, we can use the
% order to get this element deterministically.                      RM

ord_select(Element, [Head|Tail], Rest) :-
	compare(Order, Element, Head),
	ord_select(Order, Element, Tail, Head, Rest).

ord_select(=, _, Rest, _, Rest).
ord_select(>, Element, Tail, Head, [Head|Rest]) :-
	ord_select(Element, Tail, Rest).


% = ord_delete(+OrdSet, +Element, -OrdSet)
%
% as ord_select/3, but succeeds even if the Element is not in OrdSet 
%                                                                  RM

ord_delete([], _, []).
ord_delete([Head|Tail], Element, Rest) :-
	compare(Order, Element, Head),
	ord_delete(Order, Tail, Element, Head, Rest).

ord_delete(<, Tail, _, Head, [Head|Tail]).
ord_delete(=, Rest, _, _, Rest).
ord_delete(>, Tail, Element, Head, [Head|Rest]) :-
	ord_delete(Tail, Element, Rest).


% = ord_key_member(+Key, +OrdSet, ?Value)
%
% as ord_member/2, but assumes the elements of OrdSet are Key-Value
% pairs.                                                            RM

ord_key_member(Element, [Head-Data0|Tail], Data) :-
	compare(Order, Element, Head),
	ord_key_member(Order, Element, Tail, Data0, Data).

ord_key_member(=, _, _, Data, Data).
ord_key_member(>, Element, Tail, _, Data) :-
	ord_key_member(Element, Tail, Data).

% = ord_key_select(+Key, +OrdSet, -Value, -OrdSet)
%
% as ord_select/3, but assumes the elements of OrdSet are Key-Value
% pairs.                                                            RM

ord_key_select(Element, [Head-Data0|Tail], Data, Rest) :-
	compare(Order, Element, Head),
	ord_key_select(Order, Element, Tail, Head, Data0, Data, Rest).

ord_key_select(=, _, Rest, _, Data, Data, Rest).
ord_key_select(>, Element, Tail, Head, Data0, Data, [Head-Data0|Rest]) :-
	ord_key_select(Element, Tail, Data, Rest).

% = ord_key_delete(+OrdSet, +Key, -OrdSet)
%
% as ord_delete/3, but assumes the elements of OrdSet are Key-Value
% pairs.                                                            RM

ord_key_delete([], _, []).
ord_key_delete([Key-Data|Tail], Element, Rest) :-
	compare(Order, Element, Key),
	ord_key_delete(Order, Tail, Element, Key, Data, Rest).

ord_key_delete(<, Tail, _, Key, Data, [Key-Data|Tail]).
ord_key_delete(=, Rest, _, _, _, Rest).
ord_key_delete(>, Tail, Element, Key, Data, [Key-Data|Rest]) :-
	ord_key_delete(Tail, Element, Rest).

% = ord_key_insert(+OrdSet, +Key, +Data, -OrdSet)
%
% as ord_insert/3, but assumes the elements of OrdSet are Key-Value
% pairs.                                                            RM

ord_key_insert([], Key, Data, [Key-Data]).
ord_key_insert([Key-Data|Tail], Key0, Data0, Rest) :-
	compare(Order, Key0, Key),
	ord_key_insert(Order, Tail, Key0, Data0, Key, Data, Rest).

ord_key_insert(<, Tail, Key0, Data0, Key, Data, [Key0-Data0,Key-Data|Tail]).
ord_key_insert(=, Rest, Key, Data0, Key, _Data, [Key-Data0|Rest]).
ord_key_insert(>, Tail, Key0, Data0, Key, Data, [Key-Data|Rest]) :-
	ord_key_insert(Tail, Key0, Data0, Rest).


% = ord_key_union(+Map1, +Map2, ?Map3)
%
% as ord_union/3, but for ordered sets of Key-Value pairs, where Value
% is itself an ordered set. If Map1 and Map2 contain the same Key,
% Map3 will contain the ord_union of the two values.                RM

ord_key_union([], Set2, Set2).
ord_key_union([H1-V1|T1], Set2, Union) :-
	ord_key_union_2(Set2, H1, V1, T1, Union).

ord_key_union_2([], H1, V1, T1, [H1-V1|T1]).
ord_key_union_2([H2-V2|T2], H1, V1, T1, Union) :-
	compare(Order, H1, H2),
	ord_key_union_3(Order, H1, V1, T1, H2, V2, T2, Union).

ord_key_union_3(<, H1, V1, T1, H2, V2, T2, [H1-V1|Union]) :-
	ord_key_union_2(T1, H2, V2, T2, Union).
ord_key_union_3(=, H1, V1, T1, _, V2, T2, [H1-V|Union]) :-
	ord_union(V1, V2, V),
	ord_key_union(T1, T2, Union).
ord_key_union_3(>, H1, V1, T1, H2, V2, T2, [H2-V2|Union]) :-
	ord_key_union_2(T2, H1, V1, T1, Union).

% = ord_key_union_i(+Map1, +Map2, ?Map3)
%
% as ord_union/3, but for ordered sets of Key-Value pairs, where Value
% is itself an ordered set. If Map1 and Map2 contain the same Key,
% Map3 will contain the ord_interset of the two values.             RM

ord_key_union_i([], Set2, Set2).
ord_key_union_i([H1-V1|T1], Set2, Union) :-
	ord_key_union_i2(Set2, H1, V1, T1, Union).

ord_key_union_i2([], H1, V1, T1, [H1-V1|T1]).
ord_key_union_i2([H2-V2|T2], H1, V1, T1, Union) :-
	compare(Order, H1, H2),
	ord_key_union_i3(Order, H1, V1, T1, H2, V2, T2, Union).

ord_key_union_i3(<, H1, V1, T1, H2, V2, T2, [H1-V1|Union]) :-
	ord_key_union_i2(T1, H2, V2, T2, Union).
ord_key_union_i3(=, H1, V1, T1, _, V2, T2, [H1-V|Union]) :-
	ord_intersect(V1, V2, V),
	ord_key_union_i(T1, T2, Union).
ord_key_union_i3(>, H1, V1, T1, H2, V2, T2, [H2-V2|Union]) :-
	ord_key_union_i2(T2, H1, V1, T1, Union).


% = ord_key_intersect(+Map1, +Map2, ?Map3)
%
% as ord_intersect/3, but for ordered sets of Key-Value pairs, where
% Value is itself an ordered set. If Map1 and Map2 contain the same Key,
% Map3 will contain the ord_intersect of the two values.              RM

ord_key_intersect([], _, []).
ord_key_intersect([H1-V1|T1], Set2, Intersection) :-
	ord_key_intersect_2(Set2, H1, V1, T1, Intersection).

ord_key_intersect_2([], _, _, _, []).
ord_key_intersect_2([H2-V2|T2], H1, V1, T1, Intersection) :-
	compare(Order, H1, H2),
	ord_key_intersect_3(Order, H1, V1, T1, H2, V2, T2, Intersection).

ord_key_intersect_3(<, _, _, T1, H2, V2, T2, Intersection) :-
	ord_key_intersect_2(T1, H2, V2, T2, Intersection).
ord_key_intersect_3(=, H1, V1, T1, _, V2, T2, [H1-V|Intersection]) :-
	ord_intersect(V1, V2, V),
	ord_key_intersect(T1, T2, Intersection).
ord_key_intersect_3(>, H1, V1, T1, _, _, T2, Intersection) :-
	ord_key_intersect_2(T2, H1, V1, T1, Intersection).

