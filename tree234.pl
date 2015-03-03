% -*- Mode: Prolog -*-
% This file is basically a transformation of the tree234 library
% from the Mercury distribution into Prolog code. It uses first
% argument indexing wherever possible. Any errors this may have
% introduced are mine.
%
% The copyright notice of the original code is reproduced below.
%
% Additions and changes by me are marked as such by a notice followed
% by YYYYMMDD RM to indicate date and author of the changes.
%
% I am grateful to the Mercury team for providing the original library
% under LGPL                                              20030605 RM

% = SWI module declarations                               20030327 RM

:- module(tree234, [
	list_to_btree/2,		% List -> Btree
	btree_to_list/2,                % Btree -> List
	btree_init/1,			% -> Btree
	btree_delete/3,		        % Btree x Key -> Btree
	btree_remove/4,		        % Btree x Key -> Val x Btree
	btree_remove_smallest/4,        % Btree -> Key x Value x Btree
	btree_member/3,		        % Btree -> Key x Val
	btree_lookup/3,		        % Btree x Key -> Val
	btree_get/3,		        % Btree x Key -> Val
	btree_get_replace/5,		% Btree x Key x Val -> Val x Btree
	btree_lower_bound_search/4,     % Btree x Key -> Key x Val
	btree_upper_bound_search/4,     % Btree x Key -> Key x Val
	btree_lower_bound_lookup/4,     % Btree x Key -> Val
	btree_upper_bound_lookup/4,	% Btree x Key -> Val
	btree_insert/4,		        % Btree x Key x Val -> Btree
	btree_update/4,		        % Btree x Key x Val -> Btree
	btree_put/4,			% Btree x Key x Val -> Btree
	btree_keys/2,                   % Btree -> List
	btree_values/2,                 % Btree -> List
	btree_count/2,                  % Btree -> Int
	btree_map_foldl/5,              % Pred(Key x Value x A -> A) x Btree x A -> A
	btree_foldl/4,                  % Pred(Key x Value x A -> A) x Btree x A -> A
	btree_foldl2/6,                 % Pred(Key x Value x A -> A) x Btree x A -> A
	btree_map_values/3,             % Pred(Key x Value -> Value) x Btree -> Btree
	btree_merge/3,                  % Btree x Btree -> Btree    
        btree_subtract/3,               % Btree x Btree -> Btree
	btree_append_value/4            % Btree x Key x Item -> Btree
    ]).

%---------------------------------------------------------------------------%
% Copyright (C) 1994-1997,1999-2000,2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%

% tree234 - implements a map (dictionary) using 2-3-4 trees.
% main author: conway.
% stability: medium.

% See map.m for documentation.

%------------------------------------------------------------------------------%

btree_init(empty).

%------------------------------------------------------------------------------%
% = btree_member(+Tree, ?Key, ?Value)
%
% Modified the original code so that it enumerates the Key-Value pairs
% of Tree in the order of the Key values, with the smallest Key
% first.                                                    20030327 RM

btree_member(two(K0, V0, T0, T1), K, V) :-
	(
		btree_member(T0, K, V)
	;
		K = K0,
		V = V0
	;
		btree_member(T1, K, V)
	).
btree_member(three(K0, V0, K1, V1, T0, T1, T2), K, V) :-
	(
		btree_member(T0, K, V)
	;
		K = K0,
		V = V0
	;
		btree_member(T1, K, V)
	;
		K = K1,
		V = V1
	;
		btree_member(T2, K, V)
	).
btree_member(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), K, V) :-
	(
		btree_member(T0, K, V)
	;
		K = K0,
		V = V0
	;
		btree_member(T1, K, V)
	;
		K = K1,
		V = V1
	;
		btree_member(T2, K, V)
	;
		K = K2,
		V = V2
	;
		btree_member(T3, K, V)
	).

%-------------------------------------------------------------------------
%
% = btree_get(+Tree, +Key, ?Value)
%
% Get the Value corresponding to Key from Tree. Fails if Key does not 
% exist in Tree.

btree_get(two(K0, V0, T0, T1), K, V) :-
	compare(Result, K, K0),
	btree_get2(Result, V0, T0, T1, K, V).

btree_get(three(K0, V0, K1, V1, T0, T1, T2), K, V) :-
	compare(Result, K, K0),
	btree_get3(Result, V0, K1, V1, T0, T1, T2, K, V).

btree_get(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), K, V) :-
	compare(Result, K, K1),
	btree_get4(Result, K0, V0, V1, K2, V2, T0, T1, T2, T3, K, V).

btree_get2(<, _, T0, _, K, V) :-
	btree_get(T0, K, V).
btree_get2(=, V, _,  _, _, V).
btree_get2(>, _, _, T1, K, V) :-
	btree_get(T1, K, V).

btree_get3(<, _, _ , _ , T0, _ , _ , K, V) :-
	btree_get(T0, K, V).
btree_get3(=, V, _ , _ , _ , _ , _ , _, V).
btree_get3(>, _, K1, V1, _ , T1, T2, K, V) :-
	compare(Result, K, K1),
	btree_get2(Result, V1, T1, T2, K, V).

btree_get4(<, K0, V0, _, _ , _ , T0, T1, _ , _ , K, V) :-
	compare(Result, K, K0),
	btree_get2(Result, V0, T0, T1, K, V). 
btree_get4(=, _ , _ , V, _ , _ , _ , _ , _ , _ , _, V).
btree_get4(>, _ , _ , _, K2, V2, _ , _ , T2, T3, K, V) :-
	compare(Result, K, K2),
	btree_get2(Result, V2, T2, T3, K, V).

%-------------------------------------------------------------------------
%
% btree_get_replace(+Tree, +Key, ?Val, +NewVal, ?NewTree)
%
% Assigns NewVal to Key in NewTree but reports back the old Val
% for Key in Tree as well. Behaves as is defined by the clause
%
% btree_get_replace(T0, K, V0, V, T) :-
%       btree_get(T0, K, V0),
%       btree_update(T0, K, V, T).
%
% but avoids traversing Tree twice (once for lookup and once for
% update).                                                  20030327 RM

btree_get_replace(two(K0, V0, T0, T1), K, V, Val,
	          two(K0, V1, T2, T3)) :-
	compare(Result, K, K0),
	btree_get_replace2(Result, V0, V1, T0, T1, T2, T3, K, V, Val).

btree_get_replace(three(K0, V0, K1, V1, T0, T1, T2), K, V, Val, 
	          three(K0, V2, K1, V3, T3, T4, T5)) :-
	compare(Result, K, K0),
	btree_get_replace3(Result, V0, V2, K1, V1, V3,
	                   T0, T1, T2, T3, T4, T5, K, V, Val).	

btree_get_replace(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), K, V, Val,
	          four(K0, V3, K1, V4, K2, V5, T4, T5, T6, T7)) :-
	compare(Result, K, K1),
	btree_get_replace4(Result, K0, V0, V3, V1, V4, K2, V2, V5,
	                   T0, T1, T2, T3, T4, T5, T6, T7, K, V, Val).

btree_get_replace2(<, V0, V0 , T0, T1, T2, T1, K, V, Val) :-
	btree_get_replace(T0, K, V, Val, T2).
btree_get_replace2(=, V,  V1, T0, T1, T0, T1, _, V, V1).
btree_get_replace2(>, V0, V0, T0, T1, T0, T3, K, V, Val) :-
	btree_get_replace(T1, K, V, Val, T3).

btree_get_replace3(<, V0, V0, _, V1, V1, T0, T1, T2, T3, T1, T2, K, V, Val) :-
	btree_get_replace(T0, K, V, Val, T3).
btree_get_replace3(=, V0, V2, _, V1, V1, T0, T1, T2, T0, T1, T2, _, V0, V2).
btree_get_replace3(>, V0, V0, K1, V1, V3, T0, T1, T2, T0, T4, T5, K, V, Val) :-
	compare(Result, K, K1),
	btree_get_replace2(Result, V1, V3, T1, T2, T4, T5, K, V, Val).

btree_get_replace4(<, K0, V0, V3, V1, V1, _ , V2, V2,
	           T0, T1, T2, T3, T4, T5, T2, T3, K, V, Val) :-
	compare(Result, K, K0),
	btree_get_replace2(Result, V0, V3, T0, T1, T4, T5, K, V, Val).
btree_get_replace4(=, _ , V0, V0, V1, V4, _ , V2, V2,
	           T0, T1, T2, T3, T0, T1, T2, T3, _, V1, V4).
btree_get_replace4(>, _ , V0, V0, V1, V1, K2, V2, V5,
	           T0, T1, T2, T3, T0, T1, T6, T7, K, V, Val) :-
	compare(Result, K, K2),
	btree_get_replace2(Result, V2, V5, T2, T3, T6, T7, K, V, Val).

btree_lookup(T, K, V) :-
	(
	      btree_get(T, K, V0)
	->
	      V = V0
	;
	      report_lookup_error("btree_lookup: key not found.", K, V)
	).

%----------------------------------------------------------------------------
% = btree_lower_bound_search(+Tree, +LBKey, ?Key, ?Value)
%
% Search for a Key-Value pair using the LBKey.  If there is no entry
% for the given LBKey, returns the pair for the next lower Key instead.
% Fails if there is no key with the given or lower value.

btree_lower_bound_search(two(K0, V0, T0, T1), SearchK, K, V) :-
	compare(R, SearchK, K0),
	btree_lower_bound_search2(R, K0, V0, T0, T1, SearchK, K, V).

btree_lower_bound_search(three(K0, V0, K1, V1, T0, T1, T2), SearchK, K, V) :-
	compare(R, SearchK, K0),
	btree_lower_bound_search3(R, K0, V0, K1, V1, T0, T1, T2, SearchK, K, V).

btree_lower_bound_search(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3),
	                 SearchK, K, V) :-
	compare(R, SearchK, K1),
	btree_lower_bound_search4(R, K0, V0, K1, V1, K2, V2,
	                              T0, T1, T2, T3, SearchK, K, V).

btree_lower_bound_search2(<, _, _, T0, _, SearchK, K, V) :-
	btree_lower_bound_search(T0, SearchK, K, V).
btree_lower_bound_search2(=, _, V, _, _, K, K, V).
btree_lower_bound_search2(>, K0, V0, _, T1, SearchK, K, V) :-
    ( 
	btree_lower_bound_search(T1, SearchK, K, V)
    ->
	true
    ;
	K = K0,
	V = V0
    ).

btree_lower_bound_search3(<, _, _, _, _, T0, _, _, SearchK, K, V) :-
	btree_lower_bound_search(T0, SearchK, K, V).
btree_lower_bound_search3(=, _, V, _, _, _, _, _, K, K, V).
btree_lower_bound_search3(>, K0, V0, K1, V1, _, T1, T2, SearchK, K, V) :-
	compare(R, SearchK, K1),
	btree_lower_bound_search3b(R, K0, V0, K1, V1, T1, T2, SearchK, K, V).

btree_lower_bound_search3b(<, K0, V0, _, _, T1, _, SearchK, K, V) :-
    ( 
	btree_lower_bound_search(T1, SearchK, K, V)
    ->
	true
    ;
	K = K0,
	V = V0
    ).
btree_lower_bound_search3b(=, _, _, _, V, _, _, K, K, V).
btree_lower_bound_search3b(>, _, _, K1, V1, _, T2, SearchK, K, V) :-
    ( 
	btree_lower_bound_search(T2, SearchK, K, V)
    ->
	true
    ;
	K = K1,
	V = V1
    ).


btree_lower_bound_search4(<, K0, V0, _ , _ , _ , _ ,
	                     T0, T1, _ , _ , SearchK, K, V) :-
	compare(R, SearchK, K0),
	btree_lower_bound_search4a(R, K0, V0, T0, T1, SearchK, K, V).
btree_lower_bound_search4(=, _ , _ , _ , V, _ , _ ,
	                     _ , _ , _ , _, K, K, V).
btree_lower_bound_search4(>, _ , _ , K1, V1, K2, V2,
	                     _ , _ , T2, T3, SearchK, K, V) :-
	compare(R, SearchK, K2),
	btree_lower_bound_search4b(R, K1, V1, K2, V2,
	                              T2, T3, SearchK, K, V).

btree_lower_bound_search4a(<, _ , _ , T0, _ , SearchK, K, V) :-
	btree_lower_bound_search(T0, SearchK, K, V).
btree_lower_bound_search4a(=, _ , V , _ , _ , K, K, V).
btree_lower_bound_search4a(>, K0, V0, _ , T1, SearchK, K, V) :-
    (
	btree_lower_bound_search(T1, SearchK, K, V)
    -> 
	true
    ; 
	K = K0,
	V = V0
    ).

btree_lower_bound_search4b(<, K1, V1, _ , _ , T2, _, SearchK, K, V) :-
    ( 
	btree_lower_bound_search(T2, SearchK, K, V)
    -> 
	true	
    ;
	K = K1,
	V = V1
    ).
btree_lower_bound_search4b(=, _ , _ , _ , V , _ , _ , K, K, V).
btree_lower_bound_search4b(>, _ , _ , K2, V2, _ , T3, SearchK, K, V) :-
    ( 
	btree_lower_bound_search(T3, SearchK, K, V)
    -> 
	true
    ;
	K = K2,
	V = V2
    ).

btree_lower_bound_lookup(T, SearchK, K, V) :-
    ( 
	btree_lower_bound_search(T, SearchK, K0, V0)
    ->
	K = K0,
	V = V0
    ;
	report_lookup_error("tree234__lower_bound_lookup: key not found.", SearchK, V)
    ).

%--------------------------------------------------------------------------
% = btree_upper_bound_search(+Tree, +UBKey, ?Key, ?Value)
%
% Search for a Key-Value pair using the UBKey.  If there is no entry
% for the given UBKey, returns the pair for the next higher Key instead.
% Fails if there is no key with the given or higher value.

btree_upper_bound_search(two(K0, V0, T0, T1), SearchK, K, V) :-
	compare(R, SearchK, K0),
	btree_upper_bound_search2(R, K0, V0, T0, T1, SearchK, K, V).

btree_upper_bound_search(three(K0, V0, K1, V1, T0, T1, T2), SearchK, K, V) :-
	compare(R, SearchK, K0),
	btree_upper_bound_search3(R, K0, V0, K1, V1, T0, T1, T2, SearchK, K, V).

btree_upper_bound_search(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3),
	                 SearchK, K, V) :-
	compare(R, SearchK, K1),
	btree_uppper_bound_search4(R, K0, V0, K1, V1, K2, V2,
	                           T0, T1, T2, T3, SearchK, K, V).


btree_upper_bound_search2(<, K0, V0, T0, _, SearchK, K, V) :-
    ( 
	btree_upper_bound_search(T0, SearchK, K, V)
    -> 
	true
    ;
	K = K0,
	V = V0
    ).
btree_upper_bound_search2(=, _, V, _, _, K, K, V).
btree_upper_bound_search2(>, _, _, _, T1, SearchK, K, V) :-
	btree_upper_bound_search(T1, SearchK, K, V).


btree_upper_bound_search3(<, K0, V0, _, _, T0, _, _, SearchK, K, V) :-
    ( 
	btree_upper_bound_search(T0, SearchK, K, V)
    ->
	true
    ;
	K = K0,
	V = V0
    ).
btree_upper_bound_search3(=, _, V, _, _, _, _, _, K, K, V).
btree_upper_bound_search3(>, _, _, K1, V1, _, T1, T2, SearchK, K, V) :-
	compare(R, SearchK, K1),
	btree_upper_bound_search3b(R, K1, V1, T1, T2, SearchK, K, V).

btree_upper_bound_search3b(<, K1, V1, T1, _, SearchK, K, V) :-
    (	
	btree_upper_bound_search(T1, SearchK, K, V)
    ->
	true
    ;
	K = K1,
	V = V1
    ).
btree_upper_bound_search3b(=, _, V, _, _, K, K, V).
btree_upper_bound_search3b(>, _, _, _, T2, SearchK, K, V) :-
	btree_upper_bound_search(T2, SearchK, K, V).

btree_uppper_bound_search4(<, K0, V0, K1, V1, _, _,
	                      T0, T1, _, _, SearchK, K, V) :-
	compare(R, SearchK, K0),
	btree_upper_bound_search4a(R, K0, V0, K1, V1, T0, T1, SearchK, K, V).
btree_uppper_bound_search4(=, _, _, _, V, _, _,
	                      _, _, _, _, K, K, V).
btree_uppper_bound_search4(>, _, _, _, _, K2, V2,
	                      _, _, T2, T3, SearchK, K, V) :-
	compare(R, SearchK, K2),
	btree_upper_bound_search4b(R, K2, V2, T2, T3, SearchK, K, V).


btree_upper_bound_search4a(<, K0, V0, _, _, T0, _, SearchK, K, V) :-
    ( 
	btree_upper_bound_search(T0, SearchK, K, V)
    ->
	true
    ;
	K = K0,
	V = V0
    ).
btree_upper_bound_search4a(=, _, V, _, _, _, _, K, K, V).
btree_upper_bound_search4a(>, _, _, K1, V1, _, T1, SearchK, K, V) :-
    ( 
	btree_upper_bound_search(T1, SearchK, K, V)
    ->
	true
    ;
	K = K1,
	V = V1
    ).

btree_upper_bound_search4b(<, K2, V2, T2, _, SearchK, K, V) :-
    ( 
	btree_upper_bound_search(T2, SearchK, K, V)
    ->
	true
    ;
	K = K2,
	V = V2
    ).
btree_upper_bound_search4b(=, _, V, _, _, K, K, V).
btree_upper_bound_search4b(>, _, _, _, T3, SearchK, K, V) :-
	btree_upper_bound_search(T3, SearchK, K, V).

btree_upper_bound_lookup(T, SearchK, K, V) :-
     ( 
	 btree_upper_bound_search(T, SearchK, K0, V0)
     ->
	K = K0,
	V = V0
    ;
	report_lookup_error("tree234__upper_bound_lookup: key not found.", SearchK, V)
    ).

%---------------------------------------------------------------------------
%
% = btree_update(+Tree, +Key, +Value, ?NewTree)
%
% True if NewTree is identical to Tree except that Key is assigned Value in
% NewTree.
% Fails if Key does not exist in Tree.

btree_update(two(K0, V0, T0, T1), K, V,
             two(K0, V1, T2, T3)) :-
	compare(R, K, K0),
	btree_update2(R, V0, V1, T0, T1, T2, T3, K, V).

btree_update(three(K0, V0, K1, V1, T0, T1, T2), K, V,
	     three(K0, V2, K1, V3, T3, T4, T5)) :-
	compare(R, K, K0),
	btree_update3(R, V0, V2, K1, V1, V3, T0, T1, T2, T3, T4, T5, K, V).

btree_update(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), K, V,
	     four(K0, V3, K1, V4, K2, V5, T4, T5, T6, T7)) :-
	compare(R, K, K1),
	btree_update4(R, K0, K2, V0, V3, V1, V4, V2, V5,
	                 T0, T1, T2, T3, T4, T5, T6, T7, K, V).

btree_update2(<, V0, V0, T0, T1, T2, T1, K, V) :-
	btree_update(T0, K, V, T2).
btree_update2(=, _ , V , T0, T1, T0, T1, _, V).
btree_update2(>, V0, V0, T0, T1, T0, T3, K, V) :-
	btree_update(T1, K, V, T3).

btree_update3(<, V0, V0, _ , V1, V1, T0, T1, T2, T3, T1, T2, K, V) :-
	btree_update(T0, K, V, T3).
btree_update3(=, _ , V , _ , V1, V1, T0, T1, T2, T0, T1, T2, _, V).
btree_update3(>, V0, V0, K1, V1, V3, T0, T1, T2, T0, T4, T5, K, V) :-
	compare(R, K, K1),
	btree_update2(R, V1, V3, T1, T2, T4, T5, K, V).

btree_update4(<, K0, _ , V0, V3, V1, V1, V2, V2,
	         T0, T1, T2, T3, T4, T5, T2, T3, K, V) :-
	compare(R, K, K0),
	btree_update2(R, V0, V3, T0, T1, T4, T5, K, V).
btree_update4(=, _ , _ , V0, V0, _ , V , V2, V2,
	         T0, T1, T2, T3, T0, T1, T2, T3, _, V).
btree_update4(>, _ , K2, V0, V0, V1, V1, V2, V5,
	         T0, T1, T2, T3, T0, T1, T6, T7, K, V) :-
	compare(R, K, K2),
	btree_update2(R, V2, V5, T2, T3, T6, T7, K, V).

%----------------------------------------------------------------------------

% = btree_insert(+Tree, +Key, +Val, -NewTree)
% 
% True if NewTree is identical to Tree with the pair Key-Val added.
% Fails if Key already exists in Tree.

% btree_insert is implemented using the simple top-down
% approach described in eg Sedgwick which splits 4 nodes into
% two 2 nodes on the downward traversal of the tree as we
% search for the right place to insert the new key-value pair.
% We know we have the right place if the subtrees of the node
% are empty (in which case we expand the node - which will always
% work because we already split 4 nodes into 2 nodes), or if the
% tree itself is empty.
% This algorithm is O(lgN).

btree_insert(empty, K, V, two(K, V, empty, empty)).
btree_insert(two(K0, V0, T0, T1), K, V, Tout) :-
	btree_insert2(K0, V0, T0, T1, K, V, Tout).
btree_insert(three(K0, V0, K1, V1, T0, T1, T2), K, V, Tout) :-
	btree_insert3(K0, V0, K1, V1, T0, T1, T2, K, V, Tout).
btree_insert(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), K, V, Tout) :-
	compare(R, K, K1),
	btree_insert4(R, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3, K, V, Tout).

btree_insert2(K0, V0, T0, T1, K, V, Tout) :-
	compare(R, K, K0),
    (
	% T1 = empty implied by T0 = empty
	T0 = empty
    ->
	btree_insert2a(R, K0, V0, K, V, Tout)
    ;
	btree_insert2b(R, K0, V0, T0, T1, K, V, Tout)
    ).

btree_insert3(K0, V0, K1, V1, T0, T1, T2, K, V, Tout) :-
	compare(R, K, K0),
    (
	T0 = empty
	% T1 = empty implied by T0 = empty
	% T2 = empty implied by T0 = empty
    ->
	btree_insert3a(R, K0, V0, K1, V1, K, V, Tout)
    ;
	btree_insert3b(R, K0, V0, K1, V1, T0, T1, T2, K, V, Tout)
    ).

btree_insert2a(<, K0, V0, K, V, three(K, V, K0, V0, empty, empty, empty)).
btree_insert2a(>, K0, V0, K, V, three(K0, V0, K, V, empty, empty, empty)).

btree_insert2b(<, K0, V0, T0, T1, K, V, Tout) :-
	btree_insert2b1(T0, T1, K0, V0, K, V, Tout).
btree_insert2b(>, K0, V0, T0, T1, K, V, Tout) :-
	btree_insert2b2(T1, T0, K0, V0, K, V, Tout).

btree_insert2b2(two(K0, V0, T0, T1), TT0, KK0, VV0, K, V,
	        two(KK0, VV0, TT0, NewT1)) :-
	btree_insert2(K0, V0, T0, T1, K, V, NewT1).
btree_insert2b2(three(K0, V0, K1, V1, T0, T1, T2), TT0, KK0, VV0, K, V,
	        two(KK0, VV0, TT0, NewT1)) :-
	btree_insert3(K0, V0, K1, V1, T0, T1, T2, K, V, NewT1).
btree_insert2b2(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3),
                TT0, KK0, VV0, K, V,
		three(KK0, VV0, K1, V1, TT0, Mid, Right)) :-
	compare(R, K, K1),
	btree_insert5(R, K0, V0, K2, V2,
                         T0, T1, T2, T3, K, V, Mid, Right).

btree_insert2b1(two(K0, V0, T0, T1), TT1, KK0, VV0, K, V,
	        two(KK0, VV0, NewT0, TT1)) :-
	btree_insert2(K0, V0, T0, T1, K, V, NewT0).
btree_insert2b1(three(K0, V0, K1, V1, T0, T1, T2), TT1, KK0, VV0, K, V,
	        two(KK0, VV0, NewT0, TT1)) :-
	btree_insert3(K0, V0, K1, V1, T0, T1, T2, K, V, NewT0).
btree_insert2b1(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3),
	        TT1, KK0, VV0, K, V,
                three(K1, V1, KK0, VV0, Left, Mid, TT1)) :-
	compare(R, K, K1),
	btree_insert5(R, K0, V0, K2, V2,
	                 T0, T1, T2, T3, K, V, Left, Mid).

btree_insert3a(<, K0, V0, K1, V1, K, V,
                  four(K, V, K0, V0, K1, V1, empty, empty, empty, empty)).
btree_insert3a(>, K0, V0, K1, V1, K, V,
	          Tout) :-
	compare(R, K, K1),
	btree_insert3a1(R, K0, V0, K1, V1, K, V, Tout).

btree_insert3a1(<, K0, V0, K1, V1, K, V,
                   four(K0, V0, K, V, K1, V1, empty, empty, empty, empty)).
btree_insert3a1(>, K0, V0, K1, V1, K, V,
	           four(K0, V0, K1, V1, K, V, empty, empty, empty, empty)).

btree_insert3b(<, K0, V0, K1, V1, T0, T1, T2, K, V, Tout) :-
	btree_insert3b1(T0, T1, T2, K0, V0, K1, V1, K, V, Tout).
btree_insert3b(>, K0, V0, K1, V1, T0, T1, T2, K, V, Tout) :-
	compare(R, K, K1),
	btree_insert3c(R, T1, T0, T2, K0, V0, K1, V1, K, V, Tout).

btree_insert3b1(two(K0, V0, T0, T1), TT1, TT2,
                KK0, VV0, KK1, VV1, K, V,
                three(KK0, VV0, KK1, VV1, NewT0, TT1, TT2)) :-
	btree_insert2(K0, V0, T0, T1, K, V, NewT0).
btree_insert3b1(three(K0, V0, K1, V1, T0, T1, T2), TT1, TT2,
	        KK0, VV0, KK1, VV1, K, V,
		three(KK0, VV0, KK1, VV1, NewT0, TT1, TT2)) :-
	btree_insert3(K0, V0, K1, V1, T0, T1, T2, K, V, NewT0).
btree_insert3b1(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3),
	        TT1, TT2, KK0, VV0, KK1, VV1, K, V,
		four(K1, V1, KK0, VV0, KK1, VV1, Left, MidL, TT1, TT2)) :-
	compare(R, K, K1),
	btree_insert5(R, K0, V0, K2, V2, T0, T1, T2, T3,
	                    K, V, Left, MidL).

btree_insert3c(<, T1, T0, T2, K0, V0, K1, V1, K, V, Tout) :-
	btree_insert3c1(T1, T0, T2, K0, V0, K1, V1, K, V, Tout).
btree_insert3c(>, T1, T0, T2, K0, V0, K1, V1, K, V, Tout) :-
	btree_insert3c2(T2, T0, T1, K0, V0, K1, V1, K, V, Tout).

btree_insert3c1(two(K0, V0, T0, T1),
	        TT0, TT2, KK0, VV0, KK1, VV1, K, V,
		three(KK0, VV0, KK1, VV1, TT0, NewT, TT2)) :-
	btree_insert2(K0, V0, T0, T1, K, V, NewT).
btree_insert3c1(three(K0, V0, K1, V1, T0, T1, T2),
	        TT0, TT2, KK0, VV0, KK1, VV1, K, V,
		three(KK0, VV0, KK1, VV1, TT0, NewT, TT2)) :-
	btree_insert3(K0, V0, K1, V1, T0, T1, T2, K, V, NewT).
btree_insert3c1(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3),
	        TT0, TT2, KK0, VV0, KK1, VV1, K, V,
		four(KK0, VV0, K1, V1, KK1, VV1,
		     TT0, MidL, MidR, TT2)) :-
	compare(R, K, K1),
	btree_insert5(R, K0, V0, K2, V2, T0, T1, T2, T3, K, V, MidL, MidR).

btree_insert3c2(two(K0, V0, T0, T1),
	        TT0, TT1, KK0, VV0, KK1, VV1, K, V,
	        three(KK0, VV0, KK1, VV1, TT0, TT1, NewT)) :-
	btree_insert2(K0, V0, T0, T1, K, V, NewT).
btree_insert3c2(three(K0, V0, K1, V1, T0, T1, T2),
	        TT0, TT1, KK0, VV0, KK1, VV1, K, V,
		three(KK0, VV0, KK1, VV1, TT0, TT1, NewT)) :-
	btree_insert3(K0, V0, K1, V1, T0, T1, T2, K, V, NewT).
btree_insert3c2(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3),
	        TT0, TT1, KK0, VV0, KK1, VV1, K, V,
		four(KK0, VV0, KK1, VV1, K1, V1, TT0, TT1, MidR, Right)) :-
	compare(R, K, K1),
	btree_insert5(R, K0, V0, K2, V2, T0, T1, T2, T3, K, V, MidR, Right).

btree_insert4(<, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
                 K, V, two(K1, V1, NewSub0, two(K2, V2, T2, T3))) :-
	btree_insert2(K0, V0, T0, T1, K, V, NewSub0).
btree_insert4(>, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
	         K, V, two(K1, V1, two(K0, V0, T0, T1), NewSub1)) :-
	btree_insert2(K2, V2, T2, T3, K, V, NewSub1).

btree_insert5(<, K0, V0, K2, V2, T0, T1, T2, T3, K, V,
	            MidR, two(K2, V2, T2, T3)) :-
	btree_insert2(K0, V0, T0, T1, K, V, MidR).
btree_insert5(>, K0, V0, K2, V2, T0, T1, T2, T3, K, V,
	            two(K0, V0, T0, T1), Right) :-
	btree_insert2(K2, V2, T2, T3, K, V, Right).

%------------------------------------------------------------------------------%

% btree_put uses the same algorithm as used for btree_insert,
% except that instead of failing for equal keys, we replace the value.

btree_put(empty, K, V, two(K, V, empty, empty)).
btree_put(two(K0, V0, T0, T1), K, V, Tout) :-
	btree_put2(K0, V0, T0, T1, K, V, Tout).
btree_put(three(K0, V0, K1, V1, T0, T1, T2), K, V, Tout) :-
	btree_put3(K0, V0, K1, V1, T0, T1, T2, K, V, Tout).
btree_put(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), K, V, Tout) :-
	compare(Result, K, K1),
	btree_put4(Result, K0, V0, K1, V1, K2, V2,
                           T0, T1, T2, T3, K, V, Tout).
	       
btree_put2(K0, V0, T0, T1, K, V, Tout) :-
	compare(Result, K, K0),
	(
		T0 = empty
		% T1 = empty implied by T0 = empty
	->
		btree_put2a(Result, K, V, K0, V0, Tout)
	;
	        btree_put2b(Result, K0, V0, T0, T1, K, V, Tout)
	).

btree_put2a(<, K, V, K0, V0, three(K, V, K0, V0, empty, empty, empty)).
btree_put2a(=, K, V, _ , _ , two(K, V, empty, empty)).
btree_put2a(>, K, V, K0, V0, three(K0, V0, K, V, empty, empty, empty)).

btree_put2b(<, K0, V0, T0, T1, K, V, Tout) :-
	btree_put2c(T0, T1, K0, V0, K, V, Tout).
btree_put2b(=, _ , _,  T0, T1, K, V, two(K, V, T0, T1)).
btree_put2b(>, K0, V0, T0, T1, K, V, Tout) :-
	btree_put2e(T1, T0, K0, V0, K, V, Tout).

btree_put2c(two(K0, V0, T0, T1), TT1, KK0, VV0,
	    K, V, two(KK0, VV0, NewT, TT1)) :-
	btree_put2(K0, V0, T0, T1, K, V, NewT).
btree_put2c(three(K0, V0, K1, V1, T0, T1, T2), TT1, KK0, VV0,
	    K, V, two(KK0, VV0, NewT, TT1)) :-
	btree_put3(K0, V0, K1, V1, T0, T1, T2, K, V, NewT).
btree_put2c(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), TT1, KK0, VV0, 
	    K, V, three(K1, NV1, KK0, VV0, TL, TM, TT1)) :-
	compare(Result, K, K1),
	btree_put2d(Result, K0, V0, V1, NV1, K2, V2, T0, T1, T2, T3, 
	            K, V, TL, TM).

btree_put2e(two(K0, V0, T0, T1), TT0, KK0, VV0,
	    K, V, two(KK0, VV0, TT0, NewT)) :-
	btree_put2(K0, V0, T0, T1, K, V, NewT).
btree_put2e(three(K0, V0, K1, V1, T0, T1, T2), TT0, KK0, VV0,
	    K, V, two(KK0, VV0, TT0, NewT)) :-
	btree_put3(K0, V0, K1, V1, T0, T1, T2, K, V, NewT).
btree_put2e(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), TT0, KK0, VV0, 
	    K, V, three(KK0, VV0, K1, NV1, TT0, TM, TR)) :-
	compare(Result, K, K1),
	btree_put2d(Result, K0, V0, V1, NV1, K2, V2, T0, T1, T2, T3, 
	            K, V, TM, TR).

btree_put2d(<, K0, V0, V1, V1, K2, V2, T0, T1, T2, T3, K, V, 
               NewT, two(K2, V2, T2, T3)) :-
	btree_put2(K0, V0, T0, T1, K, V, NewT).
btree_put2d(=, K0, V0, _, V, K2, V2, T0, T1, T2, T3, _K, V, 
               two(K0, V0, T0, T1), two(K2, V2, T2, T3)).
btree_put2d(>, K0, V0, V1, V1, K2, V2, T0, T1, T2, T3, K, V,
	       two(K0, V0, T0, T1), NewT) :-
	btree_put2(K2, V2, T2, T3, K, V, NewT).

btree_put3(K0, V0, K1, V1, T0, T1, T2, K, V, Tout) :-
	compare(Result, K, K0),
	(
		T0 = empty
		% T1 = empty implied by T0 = empty
		% T2 = empty implied by T0 = empty
	->
	        btree_put3a(Result, K0, V0, K1, V1, K, V, Tout)
	;
	        btree_put3b(Result, K0, V0, K1, V1, T0, T1, T2, K, V, Tout)
        ).

btree_put3a(<, K0, V0, K1, V1, K, V,
	       four(K, V, K0, V0, K1, V1, empty, empty, empty, empty)).
btree_put3a(=, _ , _ , K1, V1, K, V,
	       three(K, V, K1, V1, empty, empty, empty)).
btree_put3a(>, K0, V0, K1, V1, K, V, Tout) :-
	compare(R, K, K1),
	btree_put3a1(R, K0, V0, K1, V1, K, V, Tout).

btree_put3a1(<, K0, V0, K1, V1, K, V,
	         four(K0, V0, K, V, K1, V1, empty, empty, empty, empty)).
btree_put3a1(=, K0, V0, _ , _ , K, V,
	         three(K0, V0, K, V, empty, empty, empty)).
btree_put3a1(>, K0, V0, K1, V1, K, V,
	         four(K0, V0, K1, V1, K, V, empty, empty, empty, empty)).

btree_put3b(<, K0, V0, K1, V1, T0, T1, T2, K, V, Tout) :-
	btree_put3c(T0, K0, V0, K1, V1, T1, T2, K, V, Tout).
btree_put3b(=, _ , _ , K1, V1, T0, T1, T2, K, V,
	       three(K, V, K1, V1, T0, T1, T2)).
btree_put3b(>, K0, V0, K1, V1, T0, T1, T2, K, V, Tout) :-
	compare(R, K, K1),
	btree_put3b1(R, K0, V0, K1, V1, T0, T1, T2, K, V, Tout).

btree_put3b1(<, K0, V0, K1, V1, T0, T1, T2, K, V, Tout) :-
	btree_put3d(T1, K0, V0, K1, V1, T0, T2, K, V, Tout).
btree_put3b1(=, K0, V0, _ , _ , T0, T1, T2, K, V,
	        three(K0, V0, K, V, T0, T1, T2)).
btree_put3b1(>, K0, V0, K1, V1, T0, T1, T2, K, V, Tout) :-
	btree_put3e(T2, K0, V0, K1, V1, T0, T1, K, V, Tout).

btree_put3c(two(K0, V0, T0, T1), KK0, VV0, KK1, VV1, TT1, TT2, K, V,
            three(KK0, VV0, KK1, VV1, NewT, TT1, TT2)) :-
	btree_put2(K0, V0, T0, T1, K, V, NewT).
btree_put3c(three(K0, V0, K1, V1, T0, T1, T2),
	    KK0, VV0, KK1, VV1, TT1, TT2, K, V,
	    three(KK0, VV0, KK1, VV1, NewT, TT1, TT2)) :-
	btree_put3(K0, V0, K1, V1, T0, T1, T2, K, V, NewT).
btree_put3c(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3),
	    KK0, VV0, KK1, VV1, TT1, TT2, K, V, Tout) :-
	compare(R, K, K1),
	btree_put3c1(R, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
	                KK0, VV0, KK1, VV1, TT1, TT2, K, V, Tout).

btree_put3c1(<, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
                KK0, VV0, KK1, VV1, TT1, TT2, K, V, 
		four(K1, V1, KK0, VV0, KK1, VV1,
                     NewT, two(K2, V2, T2, T3), TT1, TT2)) :-
	btree_put2(K0, V0, T0, T1, K, V, NewT).
btree_put3c1(=, K0, V0, _, _, K2, V2, T0, T1, T2, T3,
	        KK0, VV0, KK1, VV1, TT1, TT2, K, V,
		four(K, V, KK0, VV0, KK1, VV1,
		        two(K0, V0, T0, T1), two(K2, V2, T2, T3), TT1, TT2)).
btree_put3c1(>, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
	        KK0, VV0, KK1, VV1, TT1, TT2, K, V,
		four(K1, V1, KK0, VV0, KK1, VV1,
		     two(K0, V0, T0, T1), NewT, TT1, TT2)) :-
	btree_put2(K2, V2, T2, T3, K, V, NewT).

btree_put3d(two(K0, V0, T0, T1), KK0, VV0, KK1, VV1, TT0, TT2, K, V,
	    three(KK0, VV0, KK1, VV1, TT0, NewT, TT2)) :-
	btree_put2(K0, V0, T0, T1, K, V, NewT).
btree_put3d(three(K0, V0, K1, V1, T0, T1, T2),
	    KK0, VV0, KK1, VV1, TT0, TT2, K, V,
	    three(KK0, VV0, KK1, VV1, TT0, NewT, TT2)) :-
	btree_put3(K0, V0, K1, V1, T0, T1, T2, K, V, NewT).
btree_put3d(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3),
	    KK0, VV0, KK1, VV1, TT0, TT2, K, V, Tout) :-
	compare(R, K, K1),
	btree_put3d1(R, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
	                KK0, VV0, KK1, VV1, TT0, TT2, K, V, Tout).

btree_put3d1(<, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
	        KK0, VV0, KK1, VV1, TT0, TT2, K, V,
		four(KK0, VV0, K1, V1, KK1, VV1,
		     TT0, NewT, two(K2, V2, T2, T3), TT2)) :-
	btree_put2(K0, V0, T0, T1, K, V, NewT).
btree_put3d1(=, K0, V0, _ , _ , K2, V2, T0, T1, T2, T3,
	        KK0, VV0, KK1, VV1, TT0, TT2, K, V,
		four(KK0, VV0, K,  V,  KK1, VV1,
		     TT0, two(K0, V0, T0, T1), two(K2, V2, T2, T3), TT2)).
btree_put3d1(>, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
	        KK0, VV0, KK1, VV1, TT0, TT2, K, V,
		four(KK0, VV0, K1, V1, KK1, VV1,
		     TT0, two(K0, V0, T0, T1), NewT, TT2)) :-
	btree_put2(K2, V2, T2, T3, K, V, NewT).

btree_put3e(two(K0, V0, T0, T1), KK0, VV0, KK1, VV1, TT0, TT1, K, V, 
            three(KK0, VV0, KK1, VV1, TT0, TT1, NewT)) :-
	btree_put2(K0, V0, T0, T1, K, V, NewT).
btree_put3e(three(K0, V0, K1, V1, T0, T1, T2), 
	    KK0, VV0, KK1, VV1, TT0, TT1, K, V,
	    three(KK0, VV0, KK1, VV1, TT0, TT1, NewT)) :-
	btree_put3(K0, V0, K1, V1, T0, T1, T2, K, V, NewT).
btree_put3e(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3),
	    KK0, VV0, KK1, VV1, TT0, TT1, K, V, Tout) :-
	compare(R, K, K1),
	btree_put3e1(R, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
	                KK0, VV0, KK1, VV1, TT0, TT1, K, V, Tout).

btree_put3e1(<, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
	        KK0, VV0, KK1, VV1, TT0, TT1, K, V,
		four(KK0, VV0, KK1, VV1, K1, V1,
		     TT0, TT1, NewT,two(K2, V2, T2, T3))) :-
	btree_put2(K0, V0, T0, T1, K, V, NewT).
btree_put3e1(=, K0, V0, _ , _, K2, V2, T0, T1, T2, T3,
	        KK0, VV0, KK1, VV1, TT0, TT1, K, V,
		four(KK0, VV0, KK1, VV1, K, V,
		     TT0, TT1, two(K0, V0, T0, T1), two(K2, V2, T2, T3))).
btree_put3e1(>, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
	        KK0, VV0, KK1, VV1, TT0, TT1, K, V,
		four(KK0, VV0, KK1, VV1, K1, V1,
		     TT0, TT1, two(K0, V0, T0, T1), NewT)) :-
	btree_put2(K2, V2, T2, T3, K, V, NewT).

btree_put4(<, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3, 
	      K, V, two(K1, V1, NewSub0, two(K2, V2, T2, T3))) :-
	btree_put2(K0, V0, T0, T1, K, V, NewSub0).
btree_put4(=, K0, V0, K1, _ , K2, V2, T0, T1, T2, T3,
	      _, V, four(K0, V0, K1, V, K2, V2, T0, T1, T2, T3)).
btree_put4(>, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3,
	      K, V, two(K1, V1, two(K0, V0, T0, T1), NewSub1)) :-
	btree_put2(K2, V2, T2, T3, K, V, NewSub1).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

btree_delete(Tin, K, Tout) :-
	btree_delete_2(Tin, K, Tout, _).

	% When deleting an item from a tree, the height of the tree may be
	% reduced by one. The last argument says whether this has occurred.

btree_delete_2(empty, _K, empty, no).
btree_delete_2(two(K0, V0, T0, T1), K, Tout, RH) :-
	compare(R, K, K0),
	btree_delete_2a(R, K0, V0, T0, T1, K, Tout, RH).

btree_delete_2(three(K0, V0, K1, V1, T0, T1, T2), K, Tout, RH) :-
	compare(R, K, K0),
	btree_delete_2b(R, K0, V0, K1, V1, T0, T1, T2, K, Tout, RH).

btree_delete_2(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), K, Tout, RH) :-
	compare(R, K, K1),
	btree_delete_2c(R, K0, V0, K1, V1, K2, V2,
	                   T0, T1, T2, T3, K, Tout, RH).

btree_delete_2a(<, K0, V0, T0, T1, K, Tout, RH) :-
	btree_delete_2(T0, K, NewT0, RHT0),
    ( 
	RHT0 = yes
    ->
	fix_2node_t0(T1, K0, V0, NewT0, Tout, RH)
    ;
	Tout = two(K0, V0, NewT0, T1),
	RH = no
    ).
btree_delete_2a(=, _ , _ , T0, T1, _, Tout, RH) :-
    (
	btree_remove_smallest_2(T1, ST1K, ST1V, NewT1, RHT1)
    ->
	( 
	    RHT1 = yes
	->
	    fix_2node_t1(T0, ST1K, ST1V, NewT1, Tout, RH)
	;
	    Tout = two(ST1K, ST1V, T0, NewT1),
	    RH = no
	)
    ;
	% T1 must be empty
	Tout = T0,
	RH = yes
    ).
btree_delete_2a(>, K0, V0, T0, T1, K, Tout, RH) :-
	btree_delete_2(T1, K, NewT1, RHT1),
    ( 
	RHT1 = yes 
    ->
	fix_2node_t1(T0, K0, V0, NewT1, Tout, RH)
    ;
	Tout = two(K0, V0, T0, NewT1),
	RH = no
    ).


btree_delete_2b(<, K0, V0, K1, V1, T0, T1, T2, K, Tout, RH) :-
	btree_delete_2(T0, K, NewT0, RHT0),
    ( 
	RHT0 = yes
    ->
	fix_3node_t0(T1, K0, V0, K1, V1, NewT0, T2, Tout, RH)
    ;
	Tout = three(K0, V0, K1, V1, NewT0, T1, T2),
	RH = no
    ).
btree_delete_2b(=, _, _, K1, V1, T0, T1, T2, _, Tout, RH) :-
    (
	btree_remove_smallest_2(T1, ST1K, ST1V, NewT1, RHT1)
    ->
	( 
	    RHT1 = yes
	->
	    fix_3node_t1(T0, ST1K, ST1V, K1, V1, NewT1, T2, Tout, RH)
	;
	    Tout = three(ST1K, ST1V, K1, V1, T0, NewT1, T2),
	    RH = no
	)
    ;
	% T1 must be empty
	Tout = two(K1, V1, T0, T2),
	RH = no
    ).
btree_delete_2b(>, K0, V0, K1, V1, T0, T1, T2, K, Tout, RH) :-
	compare(R, K, K1),
	btree_delete_2b1(R, K0, V0, K1, V1, T0, T1, T2, K, Tout, RH).

btree_delete_2b1(<, K0, V0, K1, V1, T0, T1, T2, K, Tout, RH) :-
	btree_delete_2(T1, K, NewT1, RHT1),
    ( 
	RHT1 = yes 
    ->
	fix_3node_t1(T0, K0, V0, K1, V1, NewT1, T2, Tout, RH)
    ;
	Tout = three(K0, V0, K1, V1, T0, NewT1, T2),
	RH = no
    ).
btree_delete_2b1(=, K0, V0, _, _, T0, T1, T2, _, Tout, RH) :-
    (
	btree_remove_smallest_2(T2, ST2K, ST2V, NewT2, RHT2)
    ->
	( 
	    RHT2 = yes
	->
	    fix_3node_t2(T1, K0, V0, ST2K, ST2V, T0, NewT2, Tout, RH)
	;
	    Tout = three(K0, V0, ST2K, ST2V, T0, T1, NewT2),
	    RH = no
	)
    ;
	% T2 must be empty
	Tout = two(K0, V0, T0, T1),
	RH = no
    ).
btree_delete_2b1(>, K0, V0, K1, V1, T0, T1, T2, K, Tout, RH) :-
	btree_delete_2(T2, K, NewT2, RHT2),
    ( 
	RHT2 = yes
    ->
	fix_3node_t2(T1, K0, V0, K1, V1, T0, NewT2, Tout, RH)
    ;
	Tout = three(K0, V0, K1, V1, T0, T1, NewT2),
	RH = no
    ).

btree_delete_2c(<, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3, K, Tout, RH) :-
	compare(R, K, K0),
	btree_delete_2c1(R, K0, V0, K1, V1, K2, V2,
	                    T0, T1, T2, T3, K, Tout, RH).

btree_delete_2c(=, K0, V0, _, _, K2, V2, T0, T1, T2, T3, _, Tout, RH) :-
    (
	btree_remove_smallest_2(T2, ST2K, ST2V, NewT2, RHT2)
    ->
	( 
	    RHT2 = yes
	->
	    fix_4node_t2(T3, K0, V0, ST2K, ST2V, K2, V2,
			 T0, T1, NewT2, Tout, RH)
	;
	    Tout = four(K0, V0, ST2K, ST2V, K2, V2,
			T0, T1, NewT2, T3),
	    RH = no
	)
    ;
	% T2 must be empty
	Tout = three(K0, V0, K2, V2, T0, T1, T3),
	RH = no
    ).

btree_delete_2c(>, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3, K, Tout, RH) :-
	compare(R, K, K2),
	btree_delete_2c2(R, K0, V0, K1, V1, K2, V2,
	                    T0, T1, T2, T3, K, Tout, RH).

btree_delete_2c1(<, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3, K, Tout, RH) :-
	btree_delete_2(T0, K, NewT0, RHT0),
    ( 
	RHT0 = yes
    ->
	fix_4node_t0(T1, K0, V0, K1, V1, K2, V2, NewT0, T2, T3, Tout, RH)
    ;
	Tout = four(K0, V0, K1, V1, K2, V2, NewT0, T1, T2, T3),
	RH = no
    ).

btree_delete_2c1(=, _, _, K1, V1, K2, V2, T0, T1, T2, T3, _, Tout, RH) :-
    (
	btree_remove_smallest_2(T1, ST1K, ST1V, NewT1, RHT1)
    ->
	( 
	    RHT1 = yes
	->
	    fix_4node_t1(T2, ST1K, ST1V, K1, V1, K2, V2,
                             T0, NewT1, T3, Tout, RH)
	;
	    Tout = four(ST1K, ST1V, K1, V1, K2, V2,
	                T0, NewT1, T2, T3),
	    RH = no
	)
    ;
	% T1 must be empty
	Tout = three(K1, V1, K2, V2, T0, T2, T3),
	RH = no
    ).

btree_delete_2c1(>, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3, K, Tout, RH) :-
	btree_delete_2(T1, K, NewT1, RHT1),
    ( 
	RHT1 = yes
    ->
	fix_4node_t1(T2, K0, V0, K1, V1, K2, V2,
		     T0, NewT1, T3, Tout, RH)
    ;
	Tout = four(K0, V0, K1, V1, K2, V2, T0, NewT1, T2, T3),
	RH = no
    ).

btree_delete_2c2(<, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3, K, Tout, RH) :-
	btree_delete_2(T2, K, NewT2, RHT2),
    ( 
	RHT2 = yes
    ->
	fix_4node_t2(T3, K0, V0, K1, V1, K2, V2,
			 T0, T1, NewT2, Tout, RH)
    ;
	Tout = four(K0, V0, K1, V1, K2, V2, T0, T1, NewT2, T3),
	RH = no
    ).
btree_delete_2c2(=, K0, V0, K1, V1, _, _, T0, T1, T2, T3, _, Tout, RH) :-
    (
	btree_remove_smallest_2(T3, ST3K, ST3V, NewT3, RHT3)
    ->
	( 
	    RHT3 = yes
	->
	    fix_4node_t3(T2, K0, V0, K1, V1, ST3K, ST3V,
	                     T0, T1, NewT3, Tout, RH)
	;
	    Tout = four(K0, V0, K1, V1, ST3K, ST3V,
	                T0, T1, T2, NewT3),
	    RH = no
	)
    ;
					% T3 must be empty
	Tout = three(K0, V0, K1, V1, T0, T1, T2),
	RH = no
    ).
btree_delete_2c2(>, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3, K, Tout, RH) :-
	btree_delete_2(T3, K, NewT3, RHT3),
    ( 
	RHT3 = yes
    ->
	fix_4node_t3(T2, K0, V0, K1, V1, K2, V2,
			 T0, T1, NewT3, Tout, RH)
    ;
	Tout = four(K0, V0, K1, V1, K2, V2, T0, T1, T2, NewT3),
	RH = no
    ).

%------------------------------------------------------------------------------%

	% We use the same algorithm as btree_delete.

btree_remove(Tin, K, V, Tout) :-
	btree_remove_2(Tin, K, V, Tout, _).

btree_remove_2(two(K0, V0, T0, T1), K, V, Tout, RH) :-
	compare(R, K, K0),
	btree_remove_2a(R, K0, V0, T0, T1, K, V, Tout, RH).

btree_remove_2(three(K0, V0, K1, V1, T0, T1, T2), K, V, Tout, RH) :-
	compare(R, K, K0),
	btree_remove_2b(R, K0, V0, K1, V1, T0, T1, T2, K, V, Tout, RH).

btree_remove_2(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), K, V, Tout, RH) :-
	compare(R, K, K1),
	btree_remove_2c(R, K0, V0, K1, V1, K2, V2, T0, T1, T2, T3, K, V, Tout, RH).

btree_remove_2a(<, K0, V0, T0, T1, K, V, Tout, RH) :-
	btree_remove_2(T0, K, V, NewT0, RHT0),
    ( 
	RHT0 = yes 
    ->
	fix_2node_t0(T1, K0, V0, NewT0, Tout, RH)
    ;
	Tout = two(K0, V0, NewT0, T1),
	RH = no
    ).
btree_remove_2a(=, _ , V, T0, T1, _, V, Tout, RH) :-
    (
	btree_remove_smallest_2(T1, ST1K, ST1V, NewT1, RHT1)
    ->
	( 
	    RHT1 = yes ->
	    fix_2node_t1(T0, ST1K, ST1V, NewT1, Tout, RH)
	;
	    Tout = two(ST1K, ST1V, T0, NewT1),
	    RH = no
	)
    ;
	% T1 must be empty
	Tout = T0,
	RH = yes
    ).
btree_remove_2a(>, K0, V0, T0, T1, K, V, Tout, RH) :-
	btree_remove_2(T1, K, V, NewT1, RHT1),
    ( 
	RHT1 = yes 
    ->
	fix_2node_t1(T0, K0, V0, NewT1, Tout, RH)
    ;
	Tout = two(K0, V0, T0, NewT1),
	RH = no
    ).

btree_remove_2b(<, K0, V0, K1, V1, T0, T1, T2, K, V, Tout, RH) :-
	btree_remove_2(T0, K, V, NewT0, RHT0),
    ( 
	RHT0 = yes ->
	fix_3node_t0(T1, K0, V0, K1, V1, NewT0, T2, Tout, RH)
    ;
	Tout = three(K0, V0, K1, V1, NewT0, T1, T2),
	RH = no
    ).
btree_remove_2b(=, _K0, V, K1, V1, T0, T1, T2, _K, V, Tout, RH) :-
    (
	btree_remove_smallest_2(T1, ST1K, ST1V, NewT1, RHT1)
    ->
	( 
	    RHT1 = yes 
	->
	    fix_3node_t1(T0, ST1K, ST1V, K1, V1, NewT1, T2, Tout, RH)
	;
	    Tout = three(ST1K, ST1V, K1, V1, T0, NewT1, T2),
	    RH = no
	)
    ;
	% T1 must be empty
	Tout = two(K1, V1, T0, T2),
	RH = no
    ).

btree_remove_2b(>, K0, V0, K1, V1, T0, T1, T2, K, V, Tout, RH) :-
	compare(R, K, K1),
	btree_remove_2b1(R, K0, V0, K1, V1, T0, T1, T2, K, V, Tout, RH).

btree_remove_2b1(<, K0, V0, K1, V1, T0, T1, T2, K, V, Tout, RH) :-
	btree_remove_2(T1, K, V, NewT1, RHT1),
    ( 
	RHT1 = yes 
    ->
	fix_3node_t1(T0, K0, V0, K1, V1, NewT1, T2, Tout, RH)
    ;
	Tout = three(K0, V0, K1, V1, T0, NewT1, T2),
	RH = no
    ).

btree_remove_2b1(=, K0, V0, _K1, V, T0, T1, T2, _K, V, Tout, RH) :-
    (
	btree_remove_smallest_2(T2, ST2K, ST2V, NewT2, RHT2)
    ->
	( 
	    RHT2 = yes 
	->
	    fix_3node_t2(T1, K0, V0, ST2K, ST2V, T0, NewT2, Tout, RH)
	;
	    Tout = three(K0, V0, ST2K, ST2V, T0, T1, NewT2),
	    RH = no
	)
    ;
	% T2 must be empty
	Tout = two(K0, V0, T0, T1),
	RH = no
    ).

btree_remove_2b1(>, K0, V0, K1, V1, T0, T1, T2, K, V, Tout, RH) :-
	btree_remove_2(T2, K, V, NewT2, RHT2),
    ( 
	RHT2 = yes
    ->
	fix_3node_t2(T1, K0, V0, K1, V1, T0, NewT2, Tout, RH)
    ;
	Tout = three(K0, V0, K1, V1, T0, T1, NewT2),
	RH = no
    ).

btree_remove_2c1(<, K0, V0, K1, V1, K2, V2,
	            T0, T1, T2, T3, K, V, Tout, RH) :-
	btree_remove_2(T0, K, V, NewT0, RHT0),
    ( 
	RHT0 = yes 
    ->
	fix_4node_t0(T1, K0, V0, K1, V1, K2, V2,
		         NewT0, T2, T3, Tout, RH)
    ;
	Tout = four(K0, V0, K1, V1, K2, V2, NewT0, T1, T2, T3),
	RH = no
    ).

btree_remove_2c1(=, _K0, V, K1, V1, K2, V2,
	            T0, T1, T2, T3, _K, V, Tout, RH) :-
    (
	btree_remove_smallest_2(T1, ST1K, ST1V, NewT1, RHT1)
    ->
	( 
	    RHT1 = yes 
	->
	    fix_4node_t1(T2, ST1K, ST1V, K1, V1, K2, V2,
	                     T0, NewT1, T3,Tout, RH)
	;
	    Tout = four(ST1K, ST1V, K1, V1, K2, V2, T0, NewT1, T2, T3),
	    RH = no
	)
    ;
	% T1 must be empty
	Tout = three(K1, V1, K2, V2, T0, T2, T3),
	RH = no
    ).
btree_remove_2c1(>, K0, V0, K1, V1, K2, V2,
	            T0, T1, T2, T3, K, V, Tout, RH) :-
	btree_remove_2(T1, K, V, NewT1, RHT1),
    ( 
	RHT1 = yes 
    ->
	fix_4node_t1(T2, K0, V0, K1, V1, K2, V2,
	                 T0, NewT1, T3, Tout, RH)
    ;
	Tout = four(K0, V0, K1, V1, K2, V2, T0, NewT1, T2, T3),
	RH = no
    ).

btree_remove_2c(<, K0, V0, K1, V1, K2, V2,
	           T0, T1, T2, T3, K, V, Tout, RH) :-
	compare(R, K, K0),
	btree_remove_2c1(R, K0, V0, K1, V1, K2, V2,
	                    T0, T1, T2, T3, K, V, Tout, RH).
btree_remove_2c(=, K0, V0, _K1, V, K2, V2,
	           T0, T1, T2, T3, _K, V, Tout, RH) :-
    (
	btree_remove_smallest_2(T2, ST2K, ST2V, NewT2, RHT2)
    ->
	( 
	    RHT2 = yes 
	->
	    fix_4node_t2(T3, K0, V0, ST2K, ST2V, K2, V2,
	                     T0, T1, NewT2, Tout, RH)
	;
	    Tout = four(K0, V0, ST2K, ST2V, K2, V2,
			    T0, T1, NewT2, T3),
	     RH = no
	 )
     ;
	% T2 must be empty
	Tout = three(K0, V0, K2, V2, T0, T1, T3),
	RH = no
    ).
btree_remove_2c(>, K0, V0, K1, V1, K2, V2,
	           T0, T1, T2, T3, K, V, Tout, RH) :-
	compare(R, K, K2),
	btree_remove_2c2(R, K0, V0, K1, V1, K2, V2,
	                    T0, T1, T2, T3, K, V, Tout, RH).

btree_remove_2c2(<, K0, V0, K1, V1, K2, V2,
	            T0, T1, T2, T3, K, V, Tout, RH) :-
	btree_remove_2(T2, K, V, NewT2, RHT2),
    ( 
	RHT2 = yes 
    ->
	fix_4node_t2(T3, K0, V0, K1, V1, K2, V2,
			 T0, T1, NewT2, Tout, RH)
    ;
	Tout = four(K0, V0, K1, V1, K2, V2,
			T0, T1, NewT2, T3),
	RH = no
    ).
btree_remove_2c2(=, K0, V0, K1, V1, _K2, V,
	            T0, T1, T2, T3, _K, V, Tout, RH) :-
    (
	btree_remove_smallest_2(T3, ST3K, ST3V, NewT3, RHT3)
    ->
	( 
	    RHT3 = yes 
	->
	    fix_4node_t3(T2, K0, V0, K1, V1, ST3K, ST3V,
			     T0, T1, NewT3, Tout, RH)
	;
	    Tout = four(K0, V0, K1, V1, ST3K, ST3V,
	                    T0, T1, T2, NewT3),
	    RH = no
	)
    ;
	% T3 must be empty
	Tout = three(K0, V0, K1, V1, T0, T1, T2),
	RH = no
    ).
btree_remove_2c2(>, K0, V0, K1, V1, K2, V2,
	            T0, T1, T2, T3, K, V, Tout, RH) :-
	btree_remove_2(T3, K, V, NewT3, RHT3),
    ( 
	RHT3 = yes
    ->
	fix_4node_t3(T2, K0, V0, K1, V1, K2, V2,
			 T0, T1, NewT3, Tout, RH)
    ;
	Tout = four(K0, V0, K1, V1, K2, V2, T0, T1, T2, NewT3),
	RH = no
    ).

%------------------------------------------------------------------------------%

	% The algorithm we use similar to btree_delete, except that we
	% always go down the left subtree.

btree_remove_smallest(Tin, K, V, Tout) :-
	btree_remove_smallest_2(Tin, K, V, Tout, _).

btree_remove_smallest_2(two(K0, V0, T0, T1), K, V, Tout, RH) :-
    (
	T0 = empty
    ->
	K = K0,
	V = V0,
	Tout = T1,
	RH = yes
    ;
	btree_remove_smallest_2(T0, K, V, NewT0, RHT0),
	(   
	    RHT0 = yes 
	->
	    fix_2node_t0(T1, K0, V0, NewT0, Tout, RH)
	;
	    Tout = two(K0, V0, NewT0, T1),
	    RH = no
	)
    ).

btree_remove_smallest_2(three(K0, V0, K1, V1, T0, T1, T2), K, V, Tout, RH) :-
    (
	T0 = empty
    ->
	K = K0,
	V = V0,
	Tout = two(K1, V1, T1, T2),
	RH = no
    ;
	btree_remove_smallest_2(T0, K, V, NewT0, RHT0),
	( 
	    RHT0 = yes 
	->
	    fix_3node_t0(T1, K0, V0, K1, V1, NewT0, T2, Tout, RH)
	;
	    Tout = three(K0, V0, K1, V1, NewT0, T1, T2),
	    RH = no
	)
    ).

btree_remove_smallest_2(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), K, V, Tout, RH) :-
    (
	T0 = empty
    ->
	K = K0,
	V = V0,
	Tout = three(K1, V1, K2, V2, T1, T2, T3),
	RH = no
    ;
	btree_remove_smallest_2(T0, K, V, NewT0, RHT0),
	( 
	    RHT0 = yes 
	->
	    fix_4node_t0(T1, K0, V0, K1, V1, K2, V2, NewT0, T2, T3, Tout, RH)
	;
	    Tout = four(K0, V0, K1, V1, K2, V2, NewT0, T1, T2, T3),
	    RH = no
	)
    ).

%------------------------------------------------------------------------------%

	% The input to the following group of predicates are the components
	% of a two-, three- or four-node in which the height of the indicated
	% subtree is one less that it should be. If it is possible to increase
	% the height of that subtree by moving into it elements from its
	% neighboring subtrees, do so, and return the resulting tree with RH
	% set to no. Otherwise, return a balanced tree whose height is reduced
	% by one, with RH set to yes to indicate the reduced height.

fix_2node_t0(empty, K0, V0, T0, two(K0, V0, T0, empty), yes) :-
	throw('unbalanced 234 tree').
fix_2node_t0(two(K10, V10, T10, T11), K0, V0, T0,
                  three(K0, V0, K10, V10, T0, T10, T11), yes).
fix_2node_t0(three(K10, V10, K11, V11, T10, T11, T12), K0, V0, T0,
	          two(K10, V10, two(K0, V0, T0, T10),
                                two(K11, V11, T11, T12)), no).
fix_2node_t0(four(K10, V10, K11, V11, K12, V12, T10, T11, T12, T13), K0, V0, T0,
	          two(K10, V10, two(K0, V0, T0, T10),
	                   three(K11, V11, K12, V12, T11, T12, T13)), no).

fix_2node_t1(empty, K0, V0, T1, two(K0, V0, empty, T1), yes) :-
	throw('unbalanced 234 tree').
fix_2node_t1(two(K00, V00, T00, T01), K0, V0, T1,
	          three(K00, V00, K0, V0, T00, T01, T1), yes).
fix_2node_t1(three(K00, V00, K01, V01, T00, T01, T02), K0, V0, T1,
	          two(K01, V01, two(K00, V00, T00, T01),
                                two(K0, V0, T02, T1)), no).
fix_2node_t1(four(K00, V00, K01, V01, K02, V02, T00, T01, T02, T03), K0, V0, T1,
	          two(K02, V02, three(K00, V00, K01, V01, T00, T01, T02),
		                two(K0, V0, T03, T1)), no).
fix_3node_t0(empty, K0, V0, K1, V1, T0, T2,
	     three(K0, V0, K1, V1, T0, empty, T2), no) :-
	throw('unbalanced 234 tree').
fix_3node_t0(two(K10, V10, T10, T11),
	     K0, V0, K1, V1, T0, T2,
	     two(K1, V1, three(K0, V0, K10, V10, T0, T10, T11), T2), no).
fix_3node_t0(three(K10, V10, K11, V11, T10, T11, T12),
	     K0, V0, K1, V1, T0, T2, 
	     three(K10, V10, K1, V1, two(K0, V0, T0, T10),
	                             two(K11, V11, T11, T12), T2), no).

fix_3node_t0(four(K10, V10, K11, V11, K12, V12, T10, T11, T12, T13),
	     K0, V0, K1, V1, T0, T2, 
	     three(K10, V10, K1, V1, two(K0, V0, T0, T10), 
	                             three(K11, V11, K12, V12, T11, T12, T13), T2), no).

fix_3node_t1(empty, K0, V0, K1, V1, T1, T2,
	     three(K0, V0, K1, V1, empty, T1, T2), no) :-
	throw('unbalanced 234 tree').
fix_3node_t1(two(K00, V00, T00, T01),
	     K0, V0, K1, V1, T1, T2,
	     two(K1, V1, three(K00, V00, K0, V0, T00, T01, T1), T2), no).
fix_3node_t1(three(K00, V00, K01, V01, T00, T01, T02),
	     K0, V0, K1, V1, T1, T2,
	     three(K01, V01, K1, V1, two(K00, V00, T00, T01), 
	                             two(K0, V0, T02, T1), T2), no).
fix_3node_t1(four(K00, V00, K01, V01, K02, V02, T00, T01, T02, T03),
	     K0, V0, K1, V1, T1, T2,
	     three(K02, V02, K1, V1, three(K00, V00, K01, V01, T00, T01, T02),
	                             two(K0, V0, T03, T1), T2), no).

fix_3node_t2(empty, K0, V0, K1, V1, T0, T2,
	     three(K0, V0, K1, V1, T0, empty, T2), no) :-
	throw('unbalanced 234 tree').
fix_3node_t2(two(K10, V10, T10, T11),
	     K0, V0, K1, V1, T0, T2,
	     two(K0, V0, T0, three(K10, V10, K1, V1, T10, T11, T2)), no).
fix_3node_t2(three(K10, V10, K11, V11, T10, T11, T12),
	     K0, V0, K1, V1, T0, T2,
	     three(K0, V0, K11, V11,
	           T0, two(K10, V10, T10, T11), two(K1, V1, T12, T2)), no).
fix_3node_t2(four(K10, V10, K11, V11, K12, V12, T10, T11, T12, T13),
	     K0, V0, K1, V1, T0, T2,
	     three(K0, V0, K12, V12,
	           T0, three(K10, V10, K11, V11, T10, T11, T12), two(K1, V1, T13, T2)), no).

fix_4node_t0(empty,
	     K0, V0, K1, V1, K2, V2, T0, T2, T3,
	     four(K0, V0, K1, V1, K2, V2, T0, empty, T2, T3), no) :-
	throw('unbalanced 234 tree').
fix_4node_t0(two(K10, V10, T10, T11),
	     K0, V0, K1, V1, K2, V2, T0, T2, T3,
	     three(K1, V1, K2, V2, 
	           three(K0, V0, K10, V10, T0, T10, T11), T2, T3), no).
fix_4node_t0(three(K10, V10, K11, V11, T10, T11, T12),
	     K0, V0, K1, V1, K2, V2, T0, T2, T3,
	     four(K10, V10, K1, V1, K2, V2,
	          two(K0, V0, T0, T10),
		  two(K11, V11, T11, T12), T2, T3), no).
fix_4node_t0(four(K10, V10, K11, V11, K12, V12, T10, T11, T12, T13),
	     K0, V0, K1, V1, K2, V2, T0, T2, T3,
	     four(K10, V10, K1, V1, K2, V2,
	          two(K0, V0, T0, T10),
		  three(K11, V11, K12, V12, T11, T12, T13), T2, T3), no).

fix_4node_t1(empty,
	     K0, V0, K1, V1, K2, V2, T0, T1, T3,
	     four(K0, V0, K1, V1, K2, V2, T0, T1, empty, T3), no) :-
	throw('unbalanced 234 tree').
fix_4node_t1(two(K20, V20, T20, T21),
	     K0, V0, K1, V1, K2, V2, T0, T1, T3,
	     three(K0, V0, K2, V2, T0,
	           three(K1, V1, K20, V20, T1, T20, T21), T3), no).
fix_4node_t1(three(K20, V20, K21, V21, T20, T21, T22),
	     K0, V0, K1, V1, K2, V2, T0, T1, T3,
	     four(K0, V0, K20, V20, K2, V2, T0,
	          two(K1, V1, T1, T20),
		  two(K21, V21, T21, T22), T3), no).
fix_4node_t1(four(K20, V20, K21, V21, K22, V22, T20, T21, T22, T23),
	     K0, V0, K1, V1, K2, V2, T0, T1, T3,
	     four(K0, V0, K20, V20, K2, V2, T0,
	          two(K1, V1, T1, T20),
		  three(K21, V21, K22, V22, T21, T22, T23), T3), no).

fix_4node_t2(empty,
	     K0, V0, K1, V1, K2, V2, T0, T1, T2,
	     four(K0, V0, K1, V1, K2, V2, T0, T1, T2, empty), no) :-
	throw('unbalanced 234 tree').
fix_4node_t2(two(K30, V30, T30, T31),
	     K0, V0, K1, V1, K2, V2, T0, T1, T2,
	     three(K0, V0, K1, V1, T0, T1,
	           three(K2, V2, K30, V30, T2, T30, T31)), no).
fix_4node_t2(three(K30, V30, K31, V31, T30, T31, T32),
	     K0, V0, K1, V1, K2, V2, T0, T1, T2,
	     four(K0, V0, K1, V1, K30, V30, T0, T1,
	          two(K2, V2, T2, T30),
		  two(K31, V31, T31, T32)), no).
fix_4node_t2(four(K30, V30, K31, V31, K32, V32, T30, T31, T32, T33),
	     K0, V0, K1, V1, K2, V2, T0, T1, T2,
	     four(K0, V0, K1, V1, K30, V30, T0, T1,
	          two(K2, V2, T2, T30),
		  three(K31, V31, K32, V32, T31, T32, T33)), no).

fix_4node_t3(empty,
	     K0, V0, K1, V1, K2, V2, T0, T1, T3,
	     four(K0, V0, K1, V1, K2, V2, T0, T1, empty, T3), no).
fix_4node_t3(two(K20, V20, T20, T21),
	     K0, V0, K1, V1, K2, V2, T0, T1, T3,
	     three(K0, V0, K1, V1, T0, T1,
	     three(K20, V20, K2, V2, T20, T21, T3)), no).
fix_4node_t3(three(K20, V20, K21, V21, T20, T21, T22),
	     K0, V0, K1, V1, K2, V2, T0, T1, T3,
	     four(K0, V0, K1, V1, K21, V21, T0, T1,
	          two(K20, V20, T20, T21),
		  two(K2, V2, T22, T3)), no).
fix_4node_t3(four(K20, V20, K21, V21, K22, V22, T20, T21, T22, T23),
	     K0, V0, K1, V1, K2, V2, T0, T1, T3,
	     four(K0, V0, K1, V1, K22, V22, T0, T1,
	          three(K20, V20, K21, V21, T20, T21, T22),
		  two(K2, V2, T23, T3)), no).

%------------------------------------------------------------------------------%

btree_keys(Tree, Keys) :-
	btree_keys_2(Tree, [], Keys).

btree_keys_2(empty, List, List).
btree_keys_2(two(K0, _V0, T0, T1), L0, L) :-
	btree_keys_2(T1, L0, L1),
	btree_keys_2(T0, [K0|L1], L).
btree_keys_2(three(K0, _V0, K1, _V1, T0, T1, T2), L0, L) :-
	btree_keys_2(T2, L0, L1),
	btree_keys_2(T1, [K1|L1], L2),
	btree_keys_2(T0, [K0|L2], L).
btree_keys_2(four(K0, _V0, K1, _V1, K2, _V2, T0, T1, T2, T3), L0, L) :-
	btree_keys_2(T3, L0, L1),
	btree_keys_2(T2, [K2|L1], L2),
	btree_keys_2(T1, [K1|L2], L3),
	btree_keys_2(T0, [K0|L3], L).

%------------------------------------------------------------------------------%

btree_values(Tree, Values) :-
	btree_values_2(Tree, [], Values).

btree_values_2(empty, List, List).
btree_values_2(two(_K0, V0, T0, T1), L0, L) :-
	btree_values_2(T1, L0, L1),
	btree_values_2(T0, [V0|L1], L).
btree_values_2(three(_K0, V0, _K1, V1, T0, T1, T2), L0, L) :-
	btree_values_2(T2, L0, L1),
	btree_values_2(T1, [V1|L1], L2),
	btree_values_2(T0, [V0|L2], L).
btree_values_2(four(_K0, V0, _K1, V1, _K2, V2, T0, T1, T2, T3), L0, L) :-
	btree_values_2(T3, L0, L1),
	btree_values_2(T2, [V2|L1], L2),
	btree_values_2(T1, [V1|L2], L3),
	btree_values_2(T0, [V0|L3], L).

%------------------------------------------------------------------------------%

list_to_btree(AssocList, Tree) :-
	list_to_btree_2(AssocList, empty, Tree).

list_to_btree_2([], Tree, Tree).
list_to_btree_2([K-V|Rest], Tree0, Tree) :-
	btree_put(Tree0, K, V, Tree1),
	list_to_btree_2(Rest, Tree1, Tree).

%------------------------------------------------------------------------------%

btree_to_list(Tree, AssocList) :-
	btree_to_list_2(Tree, [], AssocList).

btree_to_list_2(empty, List, List).
btree_to_list_2(two(K0, V0, T0, T1), L0, L) :-
	btree_to_list_2(T1, L0, L1),
	btree_to_list_2(T0, [K0 - V0 | L1], L).
btree_to_list_2(three(K0, V0, K1, V1, T0, T1, T2), L0, L) :-
	btree_to_list_2(T2, L0, L1),
	btree_to_list_2(T1, [K1 - V1 | L1], L2),
	btree_to_list_2(T0, [K0 - V0 | L2], L).
btree_to_list_2(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3),
					L0, L) :-
	btree_to_list_2(T3, L0, L1),
	btree_to_list_2(T2, [K2 - V2 | L1], L2),
	btree_to_list_2(T1, [K1 - V1 | L2], L3),
	btree_to_list_2(T0, [K0 - V0 | L3], L).

%------------------------------------------------------------------------------%

btree_foldl(empty, _Pred, Acc, Acc).
btree_foldl(two(K, V, T0, T1), Pred, Acc0, Acc) :-
	btree_foldl(T0, Pred, Acc0, Acc1),
	system:call(Pred, K, V, Acc1, Acc2),
	btree_foldl(T1, Pred, Acc2, Acc).
btree_foldl(three(K0, V0, K1, V1, T0, T1, T2), Pred, Acc0, Acc) :-
	btree_foldl(T0, Pred, Acc0, Acc1),
	system:call(Pred, K0, V0, Acc1, Acc2),
	btree_foldl(T1, Pred, Acc2, Acc3),
	system:call(Pred, K1, V1, Acc3, Acc4),
	btree_foldl(T2, Pred, Acc4, Acc).
btree_foldl(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), Pred, Acc0, Acc) :-
	btree_foldl(T0, Pred, Acc0, Acc1),
	system:call(Pred, K0, V0, Acc1, Acc2),
	btree_foldl(T1, Pred, Acc2, Acc3),
	system:call(Pred, K1, V1, Acc3, Acc4),
	btree_foldl(T2, Pred, Acc4, Acc5),
	system:call(Pred, K2, V2, Acc5, Acc6),
	btree_foldl(T3, Pred, Acc6, Acc).

btree_foldl2(empty, _Pred, A, A) --> [].
btree_foldl2(two(K, V, T0, T1), Pred, A0, A) -->
	btree_foldl2(T0, Pred, A0, A1),
	system:call(Pred, K, V, A1, A2),
	btree_foldl2(T1, Pred, A2, A).
btree_foldl2(three(K0, V0, K1, V1, T0, T1, T2), Pred, A0, A) -->
	btree_foldl2(T0, Pred, A0, A1),
	system:call(Pred, K0, V0, A1, A2),
	btree_foldl2(T1, Pred, A2, A3),
	system:call(Pred, K1, V1, A3, A4),
	btree_foldl2(T2, Pred, A4, A).
btree_foldl2(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), Pred, A0, A) -->
	btree_foldl2(T0, Pred, A0, A1),
	system:call(Pred, K0, V0, A1, A2),
	btree_foldl2(T1, Pred, A2, A3),
	system:call(Pred, K1, V1, A3, A4),
	btree_foldl2(T2, Pred, A4, A5),
	system:call(Pred, K2, V2, A5, A6),
	btree_foldl2(T3, Pred, A6, A).

%------------------------------------------------------------------------------%

btree_map_values(empty, _Pred, empty).
btree_map_values(two(K0, V0, Left0, Right0), Pred,
	         two(K0, W0, Left, Right)) :-
	system:call(Pred, K0, V0, W0),
	btree_map_values(Left0, Pred, Left),
	btree_map_values(Right0, Pred, Right).
btree_map_values(three(K0, V0, K1, V1, Left0, Middle0, Right0), Pred,
	         three(K0, W0, K1, W1, Left, Middle, Right)) :-
	system:call(Pred, K0, V0, W0),
	system:call(Pred, K1, V1, W1),
	btree_map_values(Left0, Pred, Left),
	btree_map_values(Middle0, Pred, Middle),
	btree_map_values(Right0, Pred, Right).
btree_map_values(four(K0, V0, K1, V1, K2, V2, Left0, LMid0, RMid0, Right0), Pred,
	         four(K0, W0, K1, W1, K2, W2, Left, LMid, RMid, Right)) :-
	system:call(Pred, K0, V0, W0),
	system:call(Pred, K1, V1, W1),
	system:call(Pred, K2, V2, W2),
	btree_map_values(Left0, Pred, Left),
	btree_map_values(LMid0, Pred, LMid),
	btree_map_values(RMid0, Pred, RMid),
	btree_map_values(Right0, Pred, Right).

%------------------------------------------------------------------------------%

btree_map_foldl(empty, _Pred, empty, A, A).
btree_map_foldl(two(K0, V0, Left0, Right0), Pred,
	           two(K0, W0, Left, Right), A0, A) :-
	btree_map_foldl(Left0, Pred, Left, A0, A1),
	system:call(Pred, K0, V0, W0, A1, A2),
	btree_map_foldl(Right0, Pred, Right, A2, A).
btree_map_foldl(three(K0, V0, K1, V1, Left0, Middle0, Right0), Pred, 
	           three(K0, W0, K1, W1, Left, Middle, Right), A0, A) :-
	btree_map_foldl(Left0, Pred, Left, A0, A1),
	system:call(Pred, K0, V0, W0, A1, A2),
	btree_map_foldl(Middle0, Pred, Middle, A2, A3),
	system:call(Pred, K1, V1, W1, A3, A4),
	btree_map_foldl(Right0, Pred, Right, A4, A).
btree_map_foldl(four(K0, V0, K1, V1, K2, V2, Left0, LMid0, RMid0, Right0), Pred,
	           four(K0, W0, K1, W1, K2, W2, Left, LMid, RMid, Right), A0, A) :-
	btree_map_foldl(Left0, Pred, Left, A0, A1),
	system:call(Pred, K0, V0, W0, A1, A2),
	btree_map_foldl(LMid0, Pred, LMid, A2, A3),
	system:call(Pred, K1, V1, W1, A3, A4),
	btree_map_foldl(RMid0, Pred, RMid, A4, A5),
	system:call(Pred, K2, V2, W2, A5, A6),
	btree_map_foldl(Right0, Pred, Right, A6, A).

%------------------------------------------------------------------------------%

	% count the number of elements in a tree
btree_count(empty, 0).
btree_count(two(_, _, T0, T1), N) :-
	btree_count(T0, N0),
	btree_count(T1, N1),
	N is 1 + N0 + N1.
btree_count(three(_, _, _, _, T0, T1, T2), N) :-
	btree_count(T0, N0),
	btree_count(T1, N1),
	btree_count(T2, N2),
	N is 2 + N0 + N1 + N2.
btree_count(four(_, _, _, _, _, _, T0, T1, T2, T3), N) :-
	btree_count(T0, N0),
	btree_count(T1, N1),
	btree_count(T2, N2),
	btree_count(T3, N3),
	N is 3 + N0 + N1 + N2 + N3.

%-----------------------------------------------------------------------------%
% These are some idiosyncratic additions to the Mercury library by me
%                                                                 20030327 RM

% = btree_merge(+Tree1, +Tree2, +Merged)
%
% True is Merged contains all Key-Value pairs of Tree1 and Tree2
% combined. If a Key is present both in Tree1 and in Tree2 the Value
% of Tree2 will replace the Value of Tree1.

btree_merge(empty, Tree, Tree).
btree_merge(two(A,B,C,D), Tree0, Tree) :-
	btree_merge2(Tree0, two(A,B,C,D), Tree).
btree_merge(three(A,B,C,D,E,F,G), Tree0, Tree) :-
	btree_merge2(Tree0, three(A,B,C,D,E,F,G), Tree).
btree_merge(four(A,B,C,D,E,F,G,H,I,J), Tree0, Tree) :-
	btree_merge2(Tree0, four(A,B,C,D,E,F,G,H,I,J), Tree).

btree_merge2(empty, Tree, Tree).
btree_merge2(two(A,B,C,D), Tree0, Tree) :-
	btree_put(Tree0, A, B, Tree1),
	btree_merge2(C, Tree1, Tree2),
	btree_merge2(D, Tree2, Tree).
btree_merge2(three(A,B,C,D,E,F,G), Tree0, Tree) :-
	btree_put(Tree0, A, B, Tree1),
	btree_put(Tree1, C, D, Tree2),
	btree_merge2(E, Tree2, Tree3),
	btree_merge2(F, Tree3, Tree4),
	btree_merge2(G, Tree4, Tree).
btree_merge2(four(A,B,C,D,E,F,G,H,I,J), Tree0, Tree) :-
	btree_put(Tree0, A, B, Tree1),
	btree_put(Tree1, C, D, Tree2),
	btree_put(Tree2, E, F, Tree3),
	btree_merge2(G, Tree3, Tree4),
	btree_merge2(H, Tree4, Tree5),
	btree_merge2(I, Tree5, Tree6),
	btree_merge2(J, Tree6, Tree).

% = btree_subtract(+Tree1, +Tree2, +NewTree).

btree_subtract(empty, Tree, Tree).
btree_subtract(two(K0, V0, T0, T1), Tree0, Tree) :-
	btree_get_replace(Tree0, K0, V1, V, Tree1),
	ordset:ord_subtract(V0, V1, V),
	btree_subtract(T0, Tree1, Tree2),
	btree_subtract(T1, Tree2, Tree).
btree_subtract(three(K0, V0, K1, V1, T0, T1, T2), Tree0, Tree) :-
	btree_get_replace(Tree0, K0, V2, V4, Tree1),
	ordset:ord_subtract(V0, V2, V4),
	btree_get_replace(Tree1, K1, V3, V5, Tree2),
	ordset:ord_subtract(V1, V3, V5),
	btree_subtract(T0, Tree2, Tree3),
	btree_subtract(T1, Tree3, Tree4),
	btree_subtract(T2, Tree4, Tree).
btree_subtract(four(K0, V0, K1, V1, K2, V2, T0, T1, T2, T3), Tree0, Tree) :-
	btree_get_replace(Tree0, K0, V3, V6, Tree1),
	ordset:ord_subtract(V0, V3, V6),
	btree_get_replace(Tree1, K1, V4, V7, Tree2),
	ordset:ord_subtract(V1, V4, V7),
	btree_get_replace(Tree2, K2, V5, V8, Tree3),
	ordset:ord_subtract(V2, V5, V8),
	btree_subtract(T0, Tree3, Tree4),
	btree_subtract(T1, Tree4, Tree5),
	btree_subtract(T2, Tree5, Tree6),
	btree_subtract(T3, Tree6, Tree).

btree_append_value(T0, K, A, T) :-
    (
	btree_get_replace(T0, K, V0, [A|V0], T)
    ->
	true
    ;
	btree_put(T0, K, [A], T)
    ).

% = report_lookup_error(+String, +Key, ?Value)
%
% raise an exception when a lookup fails.

report_lookup_error(MsgS, K, V) :-
	name(K, KS),
    ( 
	var(V)
    ->
	VS = [95]
    ;
	name(V, VS)
    ),
	append(KS, [32|VS], KVS),
	append(MsgS, [32|KVS], ExcS),
	name(Exc, ExcS),
	throw(Exc).
