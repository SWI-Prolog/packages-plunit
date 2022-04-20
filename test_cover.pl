/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           https://www.swi-prolog.org
    Copyright (c)  2006-2022, University of Amsterdam
                              VU University Amsterdam
                              SWI-Prolog Solutions b.v.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(prolog_cover,
          [ show_coverage/1,            % :Goal
            show_coverage/2             % :Goal, +Modules
          ]).
:- autoload(library(apply), [exclude/3, maplist/2, convlist/3]).
:- autoload(library(edinburgh), [nodebug/0]).
:- autoload(library(ordsets),
            [ord_intersect/2, ord_intersection/3, ord_subtract/3]).
:- autoload(library(pairs), [group_pairs_by_key/2]).
:- autoload(library(ansi_term), [ansi_format/3]).
:- autoload(library(filesex), [directory_file_path/3, make_directory_path/1]).
:- autoload(library(lists), [append/3]).
:- autoload(library(option), [option/2, option/3]).
:- autoload(library(readutil), [read_line_to_string/2]).
:- use_module(prolog_breakpoints, []).

:- set_prolog_flag(generate_debug_info, false).

/** <module> Clause coverage analysis

The purpose of this module is to find which part of the program has been
used by a certain goal. Usage is defined   in terms of clauses for which
the _head unification_ succeeded. For each clause  we count how often it
succeeded and how often it  failed.  In   addition  we  track  all _call
sites_, creating goal-by-goal annotated clauses.

This module relies on the  SWI-Prolog   tracer  hooks. It modifies these
hooks and collects the results, after   which  it restores the debugging
environment.  This has some limitations:

        * The performance degrades significantly (about 10 times)
        * It is not possible to use the debugger during coverage analysis
        * The cover analysis tool is currently not thread-safe.

The result is  represented  as  a   list  of  clause-references.  As the
references to clauses of dynamic predicates  cannot be guaranteed, these
are omitted from the result.

@bug    Relies heavily on SWI-Prolog internals. We have considered using
        a meta-interpreter for this purpose, but it is nearly impossible
        to do 100% complete meta-interpretation of Prolog.  Example
        problem areas include handling cuts in control-structures
        and calls from non-interpreted meta-predicates.
*/


:- meta_predicate
    show_coverage(0),
    show_coverage(0,+).

%!  show_coverage(:Goal) is semidet.
%!  show_coverage(:Goal, +Options) is semidet.
%!  show_coverage(:Goal, +Modules:list(atom)) is semidet.
%
%   Report on coverage by Goal. Goal is executed as in once/1. Options
%   processed:
%
%     - modules(+Modules)
%       Provide a detailed report on Modules. For backwards
%       compatibility this is the same as providing a list of
%       modules in the second argument.
%     - annotate(+Bool)
%       Create an annotated file for the detailed results.
%       This is implied if the `ext` or `dir` option are
%       specified.
%     - ext(+Ext)
%       Extension to use for the annotated file. Default is
%       `.cov`.
%     - dir(+Dir)
%       Dump the annotations in the given directory.  If not
%       given, the annotated files are created in the same
%       directory as the source file.   Each clause that is
%       related to a physical line in the file is annotated
%       with one of:
%
%         | ###  | Clause was never executed.                       |
%         | ++N  | Clause was entered N times and always succeeded  |
%         | --N  | Clause was entered N times and never succeeded   |
%         | +N-M | Clause has succeeded N times and failed M times  |
%         | +N*M | Clause was entered N times and succeeded M times |
%
%       All _call sites_ are annotated using the same conventions,
%       except that `---` is used to annotate subgoals that were
%       never called.
%     - line_numbers(Boolean)
%       If `true` (default), add line numbers to the annotated file.
%     - color(Boolean)
%       Controls using ANSI escape sequences to color the output
%       in the annotated source.  Default is `true`.

show_coverage(Goal) :-
    show_coverage(Goal, []).
show_coverage(Goal, Modules) :-
    maplist(atom, Modules),
    !,
    show_coverage(Goal, [modules(Modules)]).
show_coverage(Goal, Options) :-
    clean_output(Options),
    setup_call_cleanup(
        setup_trace(State),
        once(Goal),
        cleanup_trace(State, Options)).

setup_trace(state(Visible, Leash, Ref)) :-
    nb_setval(cover_count, 0),
    nb_setval(cover_enter, [](0)),
    nb_setval(cover_exits, [](0)),
    set_prolog_flag(coverage_analysis, true),
    asserta((user:prolog_trace_interception(Port, Frame, _, continue) :-
                    prolog_cover:assert_cover(Port, Frame)), Ref),
    port_mask([unify,exit,call], Mask),
    '$visible'(Visible, Mask),
    '$leash'(Leash, Mask),
    trace.

port_mask([], 0).
port_mask([H|T], Mask) :-
    port_mask(T, M0),
    '$syspreds':port_name(H, Bit),
    Mask is M0 \/ Bit.

cleanup_trace(state(Visible, Leash, Ref), Options) :-
    nodebug,
    '$visible'(_, Visible),
    '$leash'(_, Leash),
    erase(Ref),
    set_prolog_flag(coverage_analysis, false),
    covered(Succeeded, Failed),
    (   report_hook(Succeeded, Failed)
    ->  true
    ;   file_coverage(Succeeded, Failed, Options)
    ),
    clean_data.

%!  assert_cover(+Port, +Frame) is det.
%
%   Assert coverage of the current clause. We monitor two ports: the
%   _unify_ port to see which  clauses   we  entered, and the _exit_
%   port to see which completed successfully.

:- public assert_cover/2.

assert_cover(call, Frame) =>
    (   call_site(Frame, CallSite)
    ->  assert_event(cover_enter, CallSite)
    ;   true
    ).
assert_cover(unify, Frame) =>
    (   prolog_frame_attribute(Frame, clause, Cl),
        running_static_pred(Frame)
    ->  assert_event(cover_enter, Cl)
    ;   true
    ).
assert_cover(exit, Frame) =>
    !,
    (   prolog_frame_attribute(Frame, clause, Cl),
        running_static_pred(Frame)
    ->  assert_event(cover_exits, Cl)
    ;   true
    ),
    (   call_site(Frame, CallSite)
    ->  assert_event(cover_exits, CallSite)
    ;   true
    ).

call_site(Frame, call_site(Clause,PC,PI)) :-
    prolog_frame_attribute(Frame, pc, PC),
    prolog_frame_attribute(Frame, predicate_indicator, PI),
    prolog_frame_attribute(Frame, parent, Parent),
    running_static_pred(Parent),
    prolog_frame_attribute(Parent, clause, Clause).

%!  running_static_pred(+Frame) is semidet.
%
%   True if Frame is not running a dynamic predicate.

running_static_pred(Frame) :-
    prolog_frame_attribute(Frame, goal, Goal),
    \+ '$get_predicate_attribute'(Goal, (dynamic), 1).

%!  assert_event(+Event, +Object) is det.
%
%   Count a new event on Object.  Currently   Object  is either a clause
%   reference of a term call_site(Clause,PC).

assert_event(Event, Object) :-
    add_clause(Object, I),
    bump(Event, I).

bump(Var, I) :-
    nb_getval(Var, Array),
    arg(I, Array, Old),
    New is Old+1,
    nb_setarg(I, Array, New).

:- dynamic
    object_index/2.

add_clause(Cl, I) :-
    object_index(Cl, I),
    !.
add_clause(Cl, I) :-
    nb_getval(cover_count, I0),
    I is I0+1,
    nb_setval(cover_count, I),
    assertz(object_index(Cl, I)),
    expand_arrays(I).

expand_arrays(I) :-
    nb_getval(cover_enter, Array),
    functor(Array, _, Arity),
    I =< Arity,
    !.
expand_arrays(_) :-
    grow_array(cover_enter),
    grow_array(cover_exits).

grow_array(Name) :-
    nb_getval(Name, Array),
    functor(Array, F, Arity),
    NewSize is Arity*2,
    functor(NewArray, F, NewSize),
    copy_args(1, Arity, Array, NewArray),
    FillStart is Arity+1,
    fill_args(FillStart, NewSize, NewArray),
    nb_setval(Name, NewArray).

copy_args(I, End, From, To) :-
    I =< End,
    !,
    arg(I, From, A),
    arg(I, To, A),
    I2 is I+1,
    copy_args(I2, End, From, To).
copy_args(_, _, _, _).

fill_args(I, End, To) :-
    I =< End,
    !,
    arg(I, To, 0),
    I2 is I+1,
    fill_args(I2, End, To).
fill_args(_, _, _).

clean_data :-
    nb_delete(cover_count),
    nb_delete(cover_enter),
    nb_delete(cover_exits),
    retractall(object_index(_,_)).

%!  count(+Which, +Clause, -Count) is semidet.
%
%   Get event counts for Clause.

count(Which, Cl, Count) :-
    object_index(Cl, I),
    counter(Which),
    nb_getval(Which, Array),
    arg(I, Array, Count).

counter(cover_enter).
counter(cover_exits).

entered(Cl) :-
    count(cover_enter, Cl, Count),
    Count > 0.
exited(Cl) :-
    count(cover_exits, Cl, Count),
    Count > 0.

entered(Cl, Count) :-
    count(cover_enter, Cl, Count).
exited(Cl, Count) :-
    count(cover_exits, Cl, Count).

%!  covered(-Succeeded, -Failed) is det.
%
%   Collect failed and succeeded clauses.

covered(Succeeded, Failed) :-
    findall(Cl, (entered(Cl), \+exited(Cl)), Failed0),
    findall(Cl, exited(Cl), Succeeded0),
    sort(Failed0, Failed),
    sort(Succeeded0, Succeeded).


                 /*******************************
                 *           REPORTING          *
                 *******************************/

%!  file_coverage(+Succeeded, +Failed, +Options) is det.
%
%   Write a report on the clauses covered   organised by file to current
%   output. Show detailed information about   the  non-coverered clauses
%   defined in the modules Modules.

file_coverage(Succeeded, Failed, Options) :-
    format('~N~n~`=t~78|~n'),
    format('~tCoverage by File~t~78|~n'),
    format('~`=t~78|~n'),
    format('~w~t~w~64|~t~w~72|~t~w~78|~n',
           ['File', 'Clauses', '%Cov', '%Fail']),
    format('~`=t~78|~n'),
    forall(source_file(File),
           file_coverage(File, Succeeded, Failed, Options)),
    format('~`=t~78|~n').

file_coverage(File, Succeeded, Failed, Options) :-
    findall(Cl, clause_source(Cl, File, _), Clauses),
    sort(Clauses, All),
    (   ord_intersect(All, Succeeded)
    ->  true
    ;   ord_intersect(All, Failed)
    ),                                  % Clauses from this file are touched
    !,
    ord_intersection(All, Failed, FailedInFile),
    ord_intersection(All, Succeeded, SucceededInFile),
    ord_subtract(All, SucceededInFile, UnCov1),
    ord_subtract(UnCov1, FailedInFile, Uncovered),

    clean_set(All, All_wo_system),
    clean_set(Uncovered, Uncovered_wo_system),
    clean_set(FailedInFile, Failed_wo_system),

    length(All_wo_system, AC),
    length(Uncovered_wo_system, UC),
    length(Failed_wo_system, FC),

    CP is 100-100*UC/AC,
    FCP is 100*FC/AC,
    summary(File, 56, SFile),
    format('~w~t ~D~64| ~t~1f~72| ~t~1f~78|~n', [SFile, AC, CP, FCP]),
    (   list_details(File, Options),
        clean_set(SucceededInFile, Succeeded_wo_system),
        ord_union(Failed_wo_system, Succeeded_wo_system, Covered)
    ->  detailed_report(Uncovered_wo_system, Covered, File, Options)
    ;   true
    ).
file_coverage(_,_,_,_).

clean_set(Clauses, UserClauses) :-
    exclude(is_pldoc, Clauses, Clauses_wo_pldoc),
    exclude(is_system_clause, Clauses_wo_pldoc, UserClauses).

is_system_clause(Clause) :-
    clause_pi(Clause, Name),
    Name = system:_.

is_pldoc(Clause) :-
    clause_pi(Clause, _Module:Name2/_Arity),
    pldoc_predicate(Name2).

pldoc_predicate('$pldoc').
pldoc_predicate('$mode').
pldoc_predicate('$pred_option').
pldoc_predicate('$exported_op').        % not really PlDoc ...

summary(String, MaxLen, Summary) :-
    string_length(String, Len),
    (   Len < MaxLen
    ->  Summary = String
    ;   SLen is MaxLen - 5,
        sub_string(String, _, SLen, 0, End),
        string_concat('...', End, Summary)
    ).


%!  clause_source(+Clause, -File, -Line) is det.
%!  clause_source(-Clause, +File, -Line) is det.

clause_source(Clause, File, Line) :-
    nonvar(Clause),
    !,
    clause_property(Clause, file(File)),
    clause_property(Clause, line_count(Line)).
clause_source(Clause, File, Line) :-
    Pred = _:_,
    source_file(Pred, File),
    \+ predicate_property(Pred, multifile),
    nth_clause(Pred, _Index, Clause),
    clause_property(Clause, line_count(Line)).
clause_source(Clause, File, Line) :-
    Pred = _:_,
    predicate_property(Pred, multifile),
    nth_clause(Pred, _Index, Clause),
    clause_property(Clause, file(File)),
    clause_property(Clause, line_count(Line)).

%!  list_details(+File, +Options) is semidet.

list_details(File, Options) :-
    option(modules(Modules), Options),
    source_file_property(File, module(M)),
    memberchk(M, Modules),
    !.
list_details(File, Options) :-
    (   source_file_property(File, module(M))
    ->  module_property(M, class(user))
    ;   true     % non-module file must be user file.
    ),
    annotate_file(Options).

annotate_file(Options) :-
    (   option(annotate(true), Options)
    ;   option(dir(_), Options)
    ;   option(ext(_), Options)
    ),
    !.

%!  detailed_report(+Uncovered, +Covered, +File:atom, +Options) is det
%
%   @arg Uncovered is a list of uncovered clauses
%   @arg Covered is a list of covered clauses

detailed_report(Uncovered, Covered, File, Options):-
    annotate_file(Options),
    !,
    convlist(line_annotation(File, uncovered), Uncovered, Annot1),
    convlist(line_annotation(File, covered),   Covered,   Annot20),
    flatten(Annot20, Annot2),
    append(Annot1, Annot2, AnnotationsLen),
    pairs_keys_values(AnnotationsLen, Annotations, Lens),
    max_list(Lens, MaxLen),
    Margin is MaxLen+1,
    annotate_file(File, Annotations, [margin(Margin)|Options]).
detailed_report(Uncovered, _, File, _Options):-
    convlist(uncovered_clause_line(File), Uncovered, Pairs),
    sort(Pairs, Pairs_sorted),
    group_pairs_by_key(Pairs_sorted, Compact_pairs),
    nl,
    file_base_name(File, Base),
    format('~2|Clauses not covered from file ~p~n', [Base]),
    format('~4|Predicate ~59|Clauses at lines ~n', []),
    maplist(print_clause_line, Compact_pairs),
    nl.

line_annotation(File, uncovered, Clause, Annotation) :-
    !,
    clause_property(Clause, file(File)),
    clause_property(Clause, line_count(Line)),
    Annotation = (Line-ansi(error,###))-3.
line_annotation(File, covered, Clause, [(Line-Annot)-Len|CallSites]) :-
    clause_property(Clause, file(File)),
    clause_property(Clause, line_count(Line)),
    entered(Clause, Entered),
    exited(Clause, Exited),
    counts_annotation(Entered, Exited, Annot, Len),
    findall(((CSLine-CSAnnot)-CSLen)-PC,
            clause_call_site_annotation(Clause, PC, CSLine, CSAnnot, CSLen),
            CallSitesPC),
    pairs_keys_values(CallSitesPC, CallSites, PCs),
    check_covered_call_sites(Clause, PCs).

counts_annotation(Entered, Exited, Annot, Len) :-
    (   Exited == Entered
    ->  format(string(Text), '++~D', [Entered]),
        Annot = ansi(comment, Text)
    ;   Exited == 0
    ->  format(string(Text), '--~D', [Entered]),
        Annot = ansi(warning, Text)
    ;   Exited < Entered
    ->  Failed is Entered - Exited,
        format(string(Text), '+~D-~D', [Exited, Failed]),
        Annot = ansi(comment, Text)
    ;   format(string(Text), '+~D*~D', [Entered, Exited]),
        Annot = ansi(fg(cyan), Text)
    ),
    string_length(Text, Len).

uncovered_clause_line(File, Clause, Name-Line) :-
    clause_property(Clause, file(File)),
    clause_pi(Clause, Name),
    clause_property(Clause, line_count(Line)).

%!  clause_pi(+Clause, -Name) is det.
%
%   Return the clause predicate indicator as Module:Name/Arity.

clause_pi(Clause, Name) :-
    clause(Module:Head, _, Clause),
    functor(Head,F,A),
    Name=Module:F/A.

print_clause_line((Module:Name/Arity)-Lines):-
    term_string(Module:Name, Complete_name),
    summary(Complete_name, 54, SName),
    format('~4|~w~t~59|~p~n', [SName/Arity, Lines]).


		 /*******************************
		 *     LINE LEVEL CALL SITES	*
		 *******************************/

clause_call_site_annotation(ClauseRef, NextPC, Line, Annot, Len) :-
    clause_call_site(ClauseRef, PC-NextPC, Line:_LPos),
    (   count(cover_enter, call_site(ClauseRef, NextPC, PI), Entered),
        count(cover_exits, call_site(ClauseRef, NextPC, PI), Exited)
    ->  counts_annotation(Entered, Exited, Annot, Len)
    ;   '$fetch_vm'(ClauseRef, PC, _, VMI),
        \+ no_annotate_call_site(VMI)
    ->  Annot = ansi(error, ---),
        Len = 3
    ).

no_annotate_call_site(i_enter).
no_annotate_call_site(i_exit).
no_annotate_call_site(i_cut).


clause_call_site(ClauseRef, PC-NextPC, Pos) :-
    clause_info(ClauseRef, File, TermPos, _NameOffset),
    '$break_pc'(ClauseRef, PC, NextPC),
    '$clause_term_position'(ClauseRef, NextPC, List),
    catch(prolog_breakpoints:range(List, TermPos, SubPos), E, true),
    (   var(E)
    ->  arg(1, SubPos, A),
        file_offset_pos(File, A, Pos)
    ;   print_message(warning, coverage(clause_info(ClauseRef))),
        fail
    ).

file_offset_pos(File, A, Line:LPos) :-
    file_text(File, String),
    State = start(1, 0),
    call_nth(sub_string(String, S, _, _, "\n"), NLine),
    (   S >= A
    ->  !,
        State = start(Line, SLine),
        LPos is A-SLine
    ;   NS is S+1,
        NLine1 is NLine+1,
        nb_setarg(1, State, NLine1),
        nb_setarg(2, State, NS),
        fail
    ).

file_text(File, String) :-
    setup_call_cleanup(
        open(File, read, In),
        read_string(In, _, String),
        close(In)).

check_covered_call_sites(Clause, Reported) :-
    findall(PC, (count(_,call_site(Clause,PC,_), Count), Count > 0), Seen),
    sort(Reported, SReported),
    sort(Seen, SSeen),
    ord_subtract(SSeen, SReported, Missed),
    (   Missed == []
    ->  true
    ;   print_message(warning, coverage(unreported_call_sites(Clause, Missed)))
    ).


		 /*******************************
		 *           ANNOTATE		*
		 *******************************/

clean_output(Options) :-
    option(dir(Dir), Options),
    !,
    option(ext(Ext), Options, cov),
    format(atom(Pattern), '~w/*.~w', [Dir, Ext]),
    expand_file_name(Pattern, Files),
    maplist(delete_file, Files).
clean_output(Options) :-
    forall(source_file(File),
           clean_output(File, Options)).

clean_output(File, Options) :-
    option(ext(Ext), Options, cov),
    file_name_extension(File, Ext, CovFile),
    (   exists_file(CovFile)
    ->  E = error(_,_),
        catch(delete_file(CovFile), E,
              print_message(warning, E))
    ;   true
    ).


%!  annotate_file(+File, +Annotations, +Options) is det.
%
%   Create  an  annotated  copy  of  File.  Annotations  is  a  list  of
%   `LineNo-Annotation`,  where  `Annotation`  is  atomic    or  a  term
%   Format-Args,  optionally  embedded   in    ansi(Code,   Annotation).

annotate_file(Source, Annotations, Options) :-
    option(ext(Ext), Options, cov),
    (   option(dir(Dir), Options)
    ->  file_base_name(Source, Base),
        file_name_extension(Base, Ext, CovFile),
        directory_file_path(Dir, CovFile, CovPath),
        make_directory_path(Dir)
    ;   file_name_extension(Source, Ext, CovPath)
    ),
    keysort(Annotations, SortedAnnotations),
    setup_call_cleanup(
        open(Source, read, In),
        setup_call_cleanup(
            open(CovPath, write, Out),
            annotate(In, Out, SortedAnnotations, Options),
            close(Out)),
        close(In)).

annotate(In, Out, Annotations, Options) :-
    (   option(color(true), Options, true)
    ->  set_stream(Out, tty(true))
    ;   true
    ),
    annotate(In, Out, Annotations, 0, Options).

annotate(In, Out, Annotations, LineNo0, Options) :-
    read_line_to_string(In, Line),
    (   Line == end_of_file
    ->  true
    ;   succ(LineNo0, LineNo),
        margins(LMargin, CMargin, Options),
        line_no(LineNo, Out, LMargin),
        annotations(LineNo, Out, LMargin, Annotations, Annotations1),
        format(Out, '~t~*|~s~n', [CMargin, Line]),
        annotate(In, Out, Annotations1, LineNo, Options)
    ).

annotations(Line, Out, LMargin, [Line-Annot|T0], T) :-
    !,
    write_annotation(Out, Annot),
    (   T0 = [Line-_|_]
    ->  with_output_to(Out, ansi_format(bold, ' \u2bb0~n~t~*|', [LMargin])),
        annotations(Line, Out, LMargin, T0, T)
    ;   T = T0
    ).
annotations(_, _, _, Annots, Annots).

write_annotation(Out, ansi(Code, Fmt-Args)) =>
    with_output_to(Out, ansi_format(Code, Fmt, Args)).
write_annotation(Out, ansi(Code, Fmt)) =>
    with_output_to(Out, ansi_format(Code, Fmt, [])).
write_annotation(Out, Fmt-Args) =>
    format(Out, Fmt, Args).
write_annotation(Out, Fmt) =>
    format(Out, Fmt, []).

line_no(_, _, 0) :- !.
line_no(Line, Out, LMargin) :-
    with_output_to(Out, ansi_format(fg(127,127,127), '~t~d ~*|',
                                    [Line, LMargin])).

margins(LMargin, Margin, Options) :-
    option(line_numbers(true), Options, true),
    !,
    option(line_number_margin(LMargin), Options, 6),
    option(margin(AMargin), Options, 4),
    Margin is LMargin+AMargin.
margins(0, Margin, Options) :-
    option(margin(Margin), Options, 4).

%!  report_hook(+Succeeded, +Failed) is semidet.
%
%   This hook is called after the data   collection. It is passed a list
%   of objects that have succeeded as  well   as  a list of objects that
%   have failed.  The objects are one of
%
%     - ClauseRef
%       The specified clause
%     - call_site(ClauseRef, PC, PI)
%       A call was make in ClauseRef at the given program counter to
%       the predicate indicated by PI.

:- multifile
    report_hook/2.


		 /*******************************
		 *             MESSAGES		*
		 *******************************/

:- multifile
    prolog:message//1.

prolog:message(coverage(clause_info(ClauseRef))) -->
    [ 'Inconsistent clause info for '-[] ],
    clause_msg(ClauseRef).
prolog:message(coverage(unreported_call_sites(ClauseRef, PCList))) -->
    [ 'Failed to report call sites for '-[] ],
    clause_msg(ClauseRef),
    [ nl, '  Missed at these PC offsets: ~p'-[PCList] ].

clause_msg(ClauseRef) -->
    { clause_pi(ClauseRef, PI),
      clause_property(ClauseRef, file(File)),
      clause_property(ClauseRef, line_count(Line))
    },
    [ '~p at'-[PI], nl, '  ', url(File:Line) ].
