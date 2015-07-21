:- module(options, [term_application/1,
		    lexicon_separator/1,
		    hybrid_pros/1,
		    hybrid_connective/4,
		    hybrid_epsilon/1,
		    hybrid_concat/1,
		    hybrid_item_start/1,
		    hybrid_item_mid/1,
		    hybrid_item_end/1,
		    d_separator/1,
		    d_concat/1,
		    d_epsilon/1,
		    output_indices/1,
		    geometry/1,
		    eta_short/1,
		    generate_diagnostics/1]).

% =====================================================
% =          parameters for semantic output           =
% =====================================================

% set this option to "prolog_like" for a Prolog-like output; this will portray terms like
% ((f y) x) as f(x,y)

term_application(prolog_like).
% term_application(lambda_like).

%lexicon_separator(' - ').
lexicon_separator(' :: ').

% =====================================================
% = parameters for hybrid type-logical grammar output =
% =====================================================

% = hybrid_pros
%
% This flag controls how the prosodic lambda term of hybrid type-logical grammars are output to LaTeX.
%
% When set of "pure", lambda terms are converted to pure lambda terms (without either the empty string
% "epsilon" or the explicit concatenation operation "+".
%
% When set to "simple", pure lambda terms are converted, whenever possible, to simple lambda terms
% using concatenation "+" and the empty string "epsilon".

%hybrid_pros(pure).
hybrid_pros(simple).


% this option allows you to choose how to display the ACG/lambda grammar/hybrid type-logical
% grammar "|" or "-o" connective.
% A connective h(A,B) will be displayed by portraying, from left-to-right one of the
% subformulas (A or B) then a Prolog atom (passed to LaTeX directly), then the other
% subformula.

hybrid_connective(h(A,B), A, '|', B).             % hybrid type-logical grammar style
%hybrid_connective(h(A,B), B, '\\multimap ', A).   % ACG/lambda grammar style

% these options allow you to customise the LaTeX display of the empty string "epsilon" and
% the concatenation "+"; the only argument of these predicates is a single Prolog atom which
% will be sent to LaTeX (we need a double backslash for LaTeX commands, due to the Prolog
% meaning of the backslash).
%
% NOTE: these options make sense only when the option the file translations.pl has the option
%
% "hybrid_pros(simple)."
%
% For hybrid_pros(pure), there is no effect.

hybrid_epsilon('\\epsilon').
hybrid_concat('\\circ').

% customize the display of items in hybrid proofs

% = single-line Pros:Formula
%
%hybrid_item_start('').
%hybrid_item_mid(':').
%hybrid_item_end('').

% = separate line for Pros and Formula
%
hybrid_item_start('\\begin{array}{l}').
hybrid_item_mid('\\\\').
hybrid_item_end('\\end{array}').

% =====================================================
% =    parameters for Displacement calculus output    =
% =====================================================

% these options allow you to customise the LaTeX display of Displacement calculus
% string labels, we can use a symbol for the separator, for concatenation and for the
% empty string, with d_separator, d_concat and d_epsilon respectively.

% this option uses the +, 1, 0 operations, though it doesn't simplify "+0"
%d_separator('+1+').
%d_concat('+').
%d_epsilon(0).
d_separator(',').
d_concat('\\ ').
d_epsilon('\\epsilon').


% =====================================================
% =          parameters for axiom link trace          =
% =====================================================


% set this option to "yes" to ouput unique identifier indices of atomic formulas (useful for
% debugging)

%output_indices(yes).

output_indices(no).

% =====================================================
% =            parameters LaTeX paper size            =
% =====================================================

% the argument to the predicate geometry/1 is passed as an argument to the LaTeX geometry package.
% so very wide page lenghts are preset; comment out all but the desired choice.
% geometry(a2paper).
geometry(a1paper).
% geometry('paperwidth=200cm,textwidth=195cm').
% geometry('paperwidth=300cm,textwidth=295cm').
% geometry('paperwidth=400cm,textwidth=395cm').
% geometry('paperwidth=500cm,textwidth=495cm').


% =====================================================
% =          parameters for proof generation          =
% =====================================================

% set this flag to anything but true to obtain long normal form natural deduction
% proofs.

eta_short(true).



% set this flag to true to obtain a proof trace of the sequent proof generation
%
%generate_diagnostics(true).
generate_diagnostics(false).
