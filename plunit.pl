/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2006-2023, University of Amsterdam
			      VU University Amsterdam
			      CWI, Amsterdam
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

:- module(plunit,
	  [ set_test_options/1,         % +Options
	    begin_tests/1,              % +Name
	    begin_tests/2,              % +Name, +Options
	    end_tests/1,                % +Name
	    run_tests/0,                % Run all tests
	    run_tests/1,                % Run named test-set
	    load_test_files/1,          % +Options
	    running_tests/0,            % Prints currently running test
	    current_test/5,             % ?Unit,?Test,?Line,?Body,?Options
	    current_test_unit/2,        % ?Unit,?Options
	    test_report/1               % +What
	  ]).

/** <module> Unit Testing

Unit testing environment for SWI-Prolog and   SICStus Prolog. For usage,
please visit https://www.swi-prolog.org/pldoc/package/plunit.
*/

:- autoload(library(statistics), [call_time/2]).
:- autoload(library(apply), [maplist/3, include/3, maplist/2, foldl/4]).
:- autoload(library(lists), [member/2, append/2, flatten/2]).
:- autoload(library(option), [option/3, option/2]).
:- autoload(library(ordsets), [ord_intersection/3]).
:- autoload(library(pairs), [group_pairs_by_key/2, pairs_values/2]).
:- autoload(library(error), [must_be/2]).
:- autoload(library(thread), [concurrent_forall/2]).
:- autoload(library(aggregate), [aggregate_all/3]).
:- autoload(library(streams), [with_output_to/3]).
:- autoload(library(time), [call_with_time_limit/2]).

:- meta_predicate
    valid_options(+, 1),
    count(0, -).

		 /*******************************
		 *    CONDITIONAL COMPILATION   *
		 *******************************/

:- discontiguous
    user:term_expansion/2.

swi     :- catch(current_prolog_flag(dialect, swi), _, fail), !.
swi     :- catch(current_prolog_flag(dialect, yap), _, fail).
sicstus :- catch(current_prolog_flag(system_type, _), _, fail).


:- if(swi).
throw_error(Error_term,Impldef) :-
    throw(error(Error_term,context(Impldef,_))).

:- set_prolog_flag(generate_debug_info, false).
current_test_flag(Name, Value) :-
    current_prolog_flag(Name, Value).

set_test_flag(Name, Value) :-
    create_prolog_flag(Name, Value, []).

% ensure expansion to avoid tracing
goal_expansion(forall(C,A),
	       \+ (C, \+ A)).
goal_expansion(current_module(Module,File),
	       module_property(Module, file(File))).

:- if(current_prolog_flag(dialect, yap)).

'$set_predicate_attribute'(_, _, _).

:- endif.
:- endif.

:- if(sicstus).
throw_error(Error_term,Impldef) :-
    throw(error(Error_term,i(Impldef))). % SICStus 3 work around

% SWI-Compatibility
:- op(700, xfx, =@=).

'$set_source_module'(_, _).

%!  current_test_flag(?Name, ?Value) is nondet.
%
%   Query  flags  that  control  the    testing   process.  Emulates
%   SWI-Prologs flags.

:- dynamic test_flag/2. % Name, Val

current_test_flag(optimise, Val) :-
    current_prolog_flag(compiling, Compiling),
    (   Compiling == debugcode ; true % TBD: Proper test
    ->  Val = false
    ;   Val = true
    ).
current_test_flag(Name, Val) :-
    test_flag(Name, Val).


%!  set_test_flag(+Name, +Value) is det.

set_test_flag(Name, Val) :-
    var(Name),
    !,
    throw_error(instantiation_error, set_test_flag(Name,Val)).
set_test_flag( Name, Val ) :-
    retractall(test_flag(Name,_)),
    asserta(test_flag(Name, Val)).

:- op(1150, fx, thread_local).

user:term_expansion((:- thread_local(PI)), (:- dynamic(PI))) :-
    prolog_load_context(module, plunit).

:- endif.

		 /*******************************
		 *            IMPORTS           *
		 *******************************/

:- initialization
   (   current_test_flag(test_options, _)
   ->  true
   ;   set_test_flag(test_options,
                     [ run(make),       % run tests on make/0
                       sto(false),
                       output(on_failure)
                     ])
   ).

%!  set_test_options(+Options)
%
%   Specifies how to deal with test suites.  Defined options are:
%
%    - load(+Load)
%      Whether or not the tests must be loaded.  Values are
%      `never`, `always`, `normal` (only if not optimised)
%
%    - run(+When)
%      When the tests are run.  Values are `manual`, `make`
%      or make(all).
%
%    - silent(+Bool)
%      If `true` (default `false`), report successful tests
%      using message level `silent`, only printing errors and
%      warnings.
%
%    - output(+When)
%      If `always`, emit all output as it is produced, if `never`,
%      suppress all output and if `on_failure`, emit the output
%      if the test fails.
%
%    - sto(+Bool)
%      How to test whether code is subject to occurs check
%      (STO).  If `false` (default), STO is not considered.
%      If `true` and supported by the hosting Prolog, code
%      is run in all supported unification mode and reported
%      if the results are inconsistent.
%
%    - cleanup(+Bool)
%      If `true` (default =false), cleanup report at the end
%      of run_tests/1.  Used to improve cooperation with
%      memory debuggers such as dmalloc.
%
%    - concurrent(+Bool)
%      If `true` (default `false`), run all tests in a unit
%      concurrently.
%
%    - jobs(Num)
%      Number of jobs to use for concurrent testing.  Defaults
%      to the number of cores.
%
%    - timeout(+Seconds)
%      Set timeout for each individual test.  This acts as a
%      default that may be overuled at the level of units or
%      individual tests.

set_test_options(Options) :-
    valid_options(Options, global_test_option),
    set_test_flag(test_options, Options).

global_test_option(load(Load)) :-
    must_be(oneof([never,always,normal]), Load).
global_test_option(output(Cond)) :-
    must_be(oneof([always,on_failure]), Cond).
global_test_option(run(When)) :-
    must_be(oneof([manual,make,make(all)]), When).
global_test_option(silent(Bool)) :-
    must_be(boolean, Bool).
global_test_option(sto(Bool)) :-
    must_be(boolean, Bool).
global_test_option(cleanup(Bool)) :-
    must_be(boolean, Bool).
global_test_option(concurrent(Bool)) :-
    must_be(boolean, Bool).
global_test_option(jobs(Count)) :-
    must_be(positive_integer, Count).
global_test_option(timeout(Number)) :-
    must_be(number, Number).


%!  loading_tests
%
%   True if tests must be loaded.

loading_tests :-
    current_test_flag(test_options, Options),
    option(load(Load), Options, normal),
    (   Load == always
    ->  true
    ;   Load == normal,
	\+ current_test_flag(optimise, true)
    ).

		 /*******************************
		 *            MODULE            *
		 *******************************/

:- dynamic
    loading_unit/4,                 % Unit, Module, File, OldSource
    current_unit/4,                 % Unit, Module, Context, Options
    test_file_for/2.                % ?TestFile, ?PrologFile

%!  begin_tests(+UnitName:atom) is det.
%!  begin_tests(+UnitName:atom, Options) is det.
%
%   Start a test-unit. UnitName is the  name   of  the test set. the
%   unit is ended by :- end_tests(UnitName).

begin_tests(Unit) :-
    begin_tests(Unit, []).

begin_tests(Unit, Options) :-
    must_be(atom, Unit),
    valid_options(Options, test_set_option),
    make_unit_module(Unit, Name),
    source_location(File, Line),
    begin_tests(Unit, Name, File:Line, Options).

:- if(swi).
begin_tests(Unit, Name, File:Line, Options) :-
    loading_tests,
    !,
    '$set_source_module'(Context, Context),
    (   current_unit(Unit, Name, Context, Options)
    ->  true
    ;   retractall(current_unit(Unit, Name, _, _)),
	assert(current_unit(Unit, Name, Context, Options))
    ),
    '$set_source_module'(Old, Name),
    '$declare_module'(Name, test, Context, File, Line, false),
    discontiguous(Name:'unit test'/4),
    '$set_predicate_attribute'(Name:'unit test'/4, trace, false),
    discontiguous(Name:'unit body'/2),
    asserta(loading_unit(Unit, Name, File, Old)).
begin_tests(Unit, Name, File:_Line, _Options) :-
    '$set_source_module'(Old, Old),
    asserta(loading_unit(Unit, Name, File, Old)).

:- else.

% we cannot use discontiguous as a goal in SICStus Prolog.

user:term_expansion((:- begin_tests(Set)),
		    [ (:- begin_tests(Set)),
		      (:- discontiguous(test/2)),
		      (:- discontiguous('unit body'/2)),
		      (:- discontiguous('unit test'/4))
		    ]).

begin_tests(Unit, Name, File:_Line, Options) :-
    loading_tests,
    !,
    (   current_unit(Unit, Name, _, Options)
    ->  true
    ;   retractall(current_unit(Unit, Name, _, _)),
	assert(current_unit(Unit, Name, -, Options))
    ),
    asserta(loading_unit(Unit, Name, File, -)).
begin_tests(Unit, Name, File:_Line, _Options) :-
    asserta(loading_unit(Unit, Name, File, -)).

:- endif.

%!  end_tests(+Name) is det.
%
%   Close a unit-test module.
%
%   @tbd    Run tests/clean module?
%   @tbd    End of file?

end_tests(Unit) :-
    loading_unit(StartUnit, _, _, _),
    !,
    (   Unit == StartUnit
    ->  once(retract(loading_unit(StartUnit, _, _, Old))),
	'$set_source_module'(_, Old)
    ;   throw_error(context_error(plunit_close(Unit, StartUnit)), _)
    ).
end_tests(Unit) :-
    throw_error(context_error(plunit_close(Unit, -)), _).

%!  make_unit_module(+Name, -ModuleName) is det.
%!  unit_module(+Name, -ModuleName) is det.

:- if(swi).

unit_module(Unit, Module) :-
    atom_concat('plunit_', Unit, Module).

make_unit_module(Unit, Module) :-
    unit_module(Unit, Module),
    (   current_module(Module),
	\+ current_unit(_, Module, _, _),
	predicate_property(Module:H, _P),
	\+ predicate_property(Module:H, imported_from(_M))
    ->  throw_error(permission_error(create, plunit, Unit),
		    'Existing module')
    ;  true
    ).

:- else.

:- dynamic
    unit_module_store/2.

unit_module(Unit, Module) :-
    unit_module_store(Unit, Module),
    !.

make_unit_module(Unit, Module) :-
    prolog_load_context(module, Module),
    assert(unit_module_store(Unit, Module)).

:- endif.

		 /*******************************
		 *           EXPANSION          *
		 *******************************/

%!  expand_test(+Name, +Options, +Body, -Clause) is det.
%
%   Expand test(Name, Options) :-  Body  into   a  clause  for
%   'unit test'/4 and 'unit body'/2.

expand_test(Name, Options0, Body,
	    [ 'unit test'(Name, Line, Options, Module:'unit body'(Id, Vars)),
	      ('unit body'(Id, Vars) :- !, Body)
	    ]) :-
    source_location(_File, Line),
    prolog_load_context(module, Module),
    atomic_list_concat([Name, '@line ', Line], Id),
    term_variables(Options0, OptionVars0), sort(OptionVars0, OptionVars),
    term_variables(Body, BodyVars0), sort(BodyVars0, BodyVars),
    ord_intersection(OptionVars, BodyVars, VarList),
    Vars =.. [vars|VarList],
    (   is_list(Options0)           % allow for single option without list
    ->  Options1 = Options0
    ;   Options1 = [Options0]
    ),
    maplist(expand_option, Options1, Options2),
    valid_options(Options2, test_option),
    valid_test_mode(Options2, Options).

expand_option(Var, _) :-
    var(Var),
    !,
    throw_error(instantiation_error,_).
expand_option(A == B, true(A==B)) :- !.
expand_option(A = B, true(A=B)) :- !.
expand_option(A =@= B, true(A=@=B)) :- !.
expand_option(A =:= B, true(A=:=B)) :- !.
expand_option(error(X), throws(error(X, _))) :- !.
expand_option(exception(X), throws(X)) :- !. % SICStus 4 compatibility
expand_option(error(F,C), throws(error(F,C))) :- !. % SICStus 4 compatibility
expand_option(true, true(true)) :- !.
expand_option(O, O).

valid_test_mode(Options0, Options) :-
    include(test_mode, Options0, Tests),
    (   Tests == []
    ->  Options = [true(true)|Options0]
    ;   Tests = [_]
    ->  Options = Options0
    ;   throw_error(plunit(incompatible_options, Tests), _)
    ).

test_mode(true(_)).
test_mode(all(_)).
test_mode(set(_)).
test_mode(fail).
test_mode(throws(_)).


%!  expand(+Term, -Clauses) is semidet.

expand(end_of_file, _) :-
    loading_unit(Unit, _, _, _),
    !,
    end_tests(Unit),                % warn?
    fail.
expand((:-end_tests(_)), _) :-
    !,
    fail.
expand(_Term, []) :-
    \+ loading_tests.
expand((test(Name) :- Body), Clauses) :-
    !,
    expand_test(Name, [], Body, Clauses).
expand((test(Name, Options) :- Body), Clauses) :-
    !,
    expand_test(Name, Options, Body, Clauses).
expand(test(Name), _) :-
    !,
    throw_error(existence_error(body, test(Name)), _).
expand(test(Name, _Options), _) :-
    !,
    throw_error(existence_error(body, test(Name)), _).

:- if(swi).
:- multifile
    system:term_expansion/2.
:- endif.

system:term_expansion(Term, Expanded) :-
    (   loading_unit(_, _, File, _)
    ->  source_location(ThisFile, _),
	(   File == ThisFile
	->  true
	;   source_file_property(ThisFile, included_in(File, _))
	),
	expand(Term, Expanded)
    ).


		 /*******************************
		 *             OPTIONS          *
		 *******************************/

:- if(swi).
:- else.
must_be(list, X) :-
    !,
    (   is_list(X)
    ->  true
    ;   is_not(list, X)
    ).
must_be(Type, X) :-
    (   call(Type, X)
    ->  true
    ;   is_not(Type, X)
    ).

is_not(Type, X) :-
    (   ground(X)
    ->  throw_error(type_error(Type, X), _)
    ;   throw_error(instantiation_error, _)
    ).
:- endif.

%!  valid_options(+Options, :Pred) is det.
%
%   Verify Options to be a list of valid options according to
%   Pred.
%
%   @throws =type_error= or =instantiation_error=.

valid_options(Options, Pred) :-
    must_be(list, Options),
    verify_options(Options, Pred).

verify_options([], _).
verify_options([H|T], Pred) :-
    (   call(Pred, H)
    ->  verify_options(T, Pred)
    ;   throw_error(domain_error(Pred, H), _)
    ).


%!  test_option(+Option) is semidet.
%
%   True if Option is a valid option for test(Name, Options).

test_option(Option) :-
    test_set_option(Option),
    !.
test_option(true(_)).
test_option(fail).
test_option(throws(_)).
test_option(all(_)).
test_option(set(_)).
test_option(nondet).
test_option(fixme(_)).
test_option(forall(X)) :-
    must_be(callable, X).
test_option(timeout(Seconds)) :-
    must_be(number, Seconds).

%!  test_option(+Option) is semidet.
%
%   True if Option is a valid option for :- begin_tests(Name,
%   Options).

test_set_option(blocked(X)) :-
    must_be(ground, X).
test_set_option(condition(X)) :-
    must_be(callable, X).
test_set_option(setup(X)) :-
    must_be(callable, X).
test_set_option(cleanup(X)) :-
    must_be(callable, X).
test_set_option(sto(V)) :-
    must_be(oneof([false,true,finite_trees,rational_trees]), V).
test_set_option(concurrent(V)) :-
    must_be(boolean, V).
test_set_option(timeout(Seconds)) :-
    must_be(number, Seconds).

		 /*******************************
		 *             UTIL		*
		 *******************************/

:- meta_predicate
       reify_tmo(0, -, +),
       reify(0, -),
       capture_output(0,-,+).

%!  reify_tmo(:Goal, -Result, +Options) is det.

reify_tmo(Goal, Result, Options) :-
    option(timeout(Time), Options),
    !,
    reify(call_with_time_limit(Time, Goal), Result0),
    (   Result0 = throw(time_limit_exceeded)
    ->  Result = throw(time_limit_exceeded(Time))
    ;   Result = Result0
    ).
reify_tmo(Goal, Result, _Options) :-
    reify(Goal, Result).

%!  reify(:Goal, -Result) is det.
%
%   Call  Goal  and  unify  Result  with   one  of  `true`,  `false`  or
%   `throw(E)`.

reify(Goal, Result) :-
    (   catch(Goal, E, true)
    ->  (   var(E)
	->  Result = true
	;   Result = throw(E)
	)
    ;   Result = false
    ).

capture_output(Goal, Output, Options) :-
    option(output(How), Options, always),
    (   How == always
    ->  call(Goal)
    ;   with_output_to(string(Output), Goal,
                       [ capture([user_output, user_error]),
                         color(true)
                       ])
    ).


		 /*******************************
		 *        RUNNING TOPLEVEL      *
		 *******************************/

:- dynamic
    test_count/1,                   % Count
    passed/5,                       % Unit, Test, Line, Det, Time
    failed/5,                       % Unit, Test, Line, Reason, Time
    timeout/5,                      % Unit, Test, Line, Limit, Time
    failed_assertion/7,             % Unit, Test, Line, ALoc, STO, Reason, Goal
    blocked/4,                      % Unit, Test, Line, Reason
    sto/4,                          % Unit, Test, Line, Results
    fixme/5,                        % Unit, Test, Line, Reason, Status
    running/5,                      % Unit, Test, Line, STO, Thread
    forall_failures/2.              % Nth, Failures

%!  run_tests is semidet.
%!  run_tests(+TestSet) is semidet.
%
%   Run tests and report about the   results.  The predicate run_tests/0
%   runs all known tests that are not blocked. The predicate run_tests/1
%   takes a specification of tests  to  run.   This  is  either a single
%   specification or a list of specifications. Each single specification
%   is either the name of  a   test-unit  or  a term <test-unit>:<test>,
%   denoting a single test within a unit.
%
%   The predicate run_tests/1 is synchronized. Concurrent testing may be
%   achieved using the relevant options.  See set_test_options/1.

run_tests :-
    findall(Unit, current_test_unit(Unit,_), Units),
    run_tests(Units).

run_tests(Set) :-
    flatten([Set], List),
    maplist(runnable_tests, List, Units),
    with_mutex(plunit, run_tests_sync(Units)).

run_tests_sync(Units) :-
    cleanup,
    count_tests(Units, Count),
    asserta(test_count(Count)),
    setup_call_cleanup(
	setup_jobs(Count),
	setup_call_cleanup(
	    setup_trap_assertions(Ref),
	    run_units_and_check_errors(Units),
	    report_and_cleanup(Ref)),
	cleanup_jobs).

%!  report_and_cleanup(+Ref)
%
%   Undo changes to the environment   (trapping  assertions), report the
%   results and cleanup.

report_and_cleanup(Ref) :-
    cleanup_trap_assertions(Ref),
    report,
    cleanup_after_test.

%!  run_units_and_check_errors(+Units) is semidet.
%
%   Run all test units and succeed if all tests passed.

run_units_and_check_errors(Units) :-
    maplist(schedule_unit, Units),
    job_wait,
    all_tests_passed(_).

%!  runnable_tests(+Spec, -Plan) is det.
%
%   Change a Unit+Test spec  into  a   plain  `Unit:Tests`  lists, where
%   blocked tests or tests whose condition   fails  are already removed.
%   Each test in `Tests` is a  term   `@(Test,Line)`,  which serves as a
%   unique identifier of the test.

:- det(runnable_tests/2).
runnable_tests(Spec, Unit:RunnableTests) :-
    unit_from_spec(Spec, Unit, Tests, Module, UnitOptions),
    (   option(blocked(Reason), UnitOptions)
    ->  info(plunit(blocked(unit(Unit, Reason)))),
        RunnableTests = []
    ;   \+ condition(Module, unit(Unit), UnitOptions)
    ->  RunnableTests = []
    ;   var(Tests)
    ->  findall(TestID,
                runnable_test(Unit, _Test, Module, TestID),
                RunnableTests)
    ;   flatten([Tests], TestList),
        findall(TestID,
                ( member(Test, TestList),
                  runnable_test(Unit,Test,Module, TestID)
                ),
                RunnableTests)
    ).

runnable_test(Unit, Test, Module, @(Test,Line)) :-
    current_test(Unit, Test, Line, _Body, TestOptions),
    (   option(blocked(Reason), TestOptions)
    ->  assert(blocked(Unit, Test, Line, Reason)),
        fail
    ;   condition(Module, test(Unit,Test,Line), TestOptions)
    ).

unit_from_spec(Unit0:Tests0, Unit, Tests, Module, Options), atom(Unit0) =>
    Unit = Unit0,
    Tests = Tests0,
    (   current_unit(Unit, Module, _Supers, Options)
    ->  true
    ;   throw_error(existence_error(unit_test, Unit), _)
    ).
unit_from_spec(Unit0, Unit, _, Module, Options), atom(Unit0) =>
    Unit = Unit0,
    (   current_unit(Unit, Module, _Supers, Options)
    ->  true
    ;   throw_error(existence_error(unit_test, Unit), _)
    ).

%!  count_tests(+Units, -Count) is det.
%
%   Count the number of tests to   run. A forall(Generator, Test) counts
%   as a single test. During the execution,   the  concrete tests of the
%   _forall_ are considered "sub tests".

count_tests(Units, Count) :-
    foldl(count_tests_in_unit, Units, 0, Count).

count_tests_in_unit(_Unit:Tests, Count0, Count) :-
    length(Tests, N),
    Count is Count0+N.

%!  run_unit(+Unit) is det.
%
%   Run a single test unit. Unit is a  term Unit:Tests, where Tests is a
%   list of tests to run.

run_unit(_Unit:[]) =>
    true.
run_unit(Unit:Tests) =>
    unit_module(Unit, Module),
    unit_options(Unit, UnitOptions),
    (   setup(Module, unit(Unit), UnitOptions)
    ->  begin_unit(Unit),
        call_time(run_unit_2(Unit, Tests), Time),
        test_summary(Unit, Summary),
	end_unit(Unit, Summary.put(time, Time)),
        cleanup(Module, UnitOptions)
    ).

begin_unit(Unit) :-
    job_info(begin(unit(Unit))),
    info(plunit(begin(Unit))).

end_unit(Unit, Summary) :-
    job_info(end(unit(Unit, Summary))),
    info(plunit(end(Unit, Summary))).

:- if(current_prolog_flag(threads, true)).
run_unit_2(Unit, Tests) :-
    unit_options(Unit, UnitOptions),
    option(concurrent(true), UnitOptions, false),
    current_test_flag(test_options, GlobalOptions),
    option(concurrent(true), GlobalOptions),
    !,
    concurrent_forall(member(Test, Tests),
                      run_test(Unit, Test)).
:- endif.
run_unit_2(Unit, Tests) :-
    forall(member(Test, Tests),
	   run_test(Unit, Test)).


unit_options(Unit, Options) :-
    current_unit(Unit, _Module, _Supers, Options).


cleanup :-
    set_flag(plunit_test, 1),
    retractall(test_count(_)),
    retractall(passed(_, _, _, _, _)),
    retractall(failed(_, _, _, _, _)),
    retractall(timeout(_, _, _, _, _)),
    retractall(failed_assertion(_, _, _, _, _, _, _)),
    retractall(blocked(_, _, _, _)),
    retractall(sto(_, _, _, _)),
    retractall(fixme(_, _, _, _, _)),
    retractall(running(_,_,_,_,_)),
    retractall(forall_failures(_,_)).

cleanup_after_test :-
    current_test_flag(test_options, Options),
    option(cleanup(Cleanup), Options, false),
    (   Cleanup == true
    ->  cleanup
    ;   true
    ).


%!  run_tests_in_files(+Files:list) is det.
%
%   Run all test-units that appear in the given Files.

run_tests_in_files(Files) :-
    findall(Unit, unit_in_files(Files, Unit), Units),
    (   Units == []
    ->  true
    ;   run_tests(Units)
    ).

unit_in_files(Files, Unit) :-
    is_list(Files),
    !,
    member(F, Files),
    absolute_file_name(F, Source,
		       [ file_type(prolog),
			 access(read),
			 file_errors(fail)
		       ]),
    unit_file(Unit, Source).


		 /*******************************
		 *         HOOKING MAKE/0       *
		 *******************************/

%!  make_run_tests(+Files)
%
%   Called indirectly from make/0 after Files have been reloaded.

make_run_tests(Files) :-
    current_test_flag(test_options, Options),
    option(run(When), Options, manual),
    (   When == make
    ->  run_tests_in_files(Files)
    ;   When == make(all)
    ->  run_tests
    ;   true
    ).

:- if(swi).

unification_capability(sto_error_incomplete).
% can detect some (almost all) STO runs
unification_capability(rational_trees).
unification_capability(finite_trees).

set_unification_capability(Cap) :-
    cap_to_flag(Cap, Flag),
    set_prolog_flag(occurs_check, Flag).

current_unification_capability(Cap) :-
    current_prolog_flag(occurs_check, Flag),
    cap_to_flag(Cap, Flag),
    !.

cap_to_flag(sto_error_incomplete, error).
cap_to_flag(rational_trees, false).
cap_to_flag(finite_trees, true).

:- else.
:- if(sicstus).

unification_capability(rational_trees).
set_unification_capability(rational_trees).
current_unification_capability(rational_trees).

:- else.

unification_capability(_) :-
    fail.

:- endif.
:- endif.

		 /*******************************
		 *      ASSERTION HANDLING      *
		 *******************************/

:- if(swi).

:- dynamic prolog:assertion_failed/2.

setup_trap_assertions(Ref) :-
    asserta((prolog:assertion_failed(Reason, Goal) :-
		    test_assertion_failed(Reason, Goal)),
	    Ref).

cleanup_trap_assertions(Ref) :-
    erase(Ref).

test_assertion_failed(Reason, Goal) :-
    thread_self(Me),
    running(Unit, Test, Line, Progress, Me),
    (   catch(get_prolog_backtrace(10, Stack), _, fail),
	assertion_location(Stack, AssertLoc)
    ->  true
    ;   AssertLoc = unknown
    ),
    current_test_flag(test_options, Options),
    report_failed_assertion(Unit, Test, Line, AssertLoc,
			    Progress, Reason, Goal, Options),
    assert_cyclic(failed_assertion(Unit, Test, Line, AssertLoc,
				   Progress, Reason, Goal)).

assertion_location(Stack, File:Line) :-
    append(_, [AssertFrame,CallerFrame|_], Stack),
    prolog_stack_frame_property(AssertFrame,
				predicate(prolog_debug:assertion/1)),
    !,
    prolog_stack_frame_property(CallerFrame, location(File:Line)).

report_failed_assertion(Unit, Test, Line, AssertLoc,
			Progress, Reason, Goal, _Options) :-
    print_message(
	error,
	plunit(failed_assertion(Unit, Test, Line, AssertLoc,
				Progress, Reason, Goal))).

:- else.

setup_trap_assertions(_).
cleanup_trap_assertions(_).

:- endif.


		 /*******************************
		 *         RUNNING A TEST       *
		 *******************************/

%!  run_test(+Unit, +Test) is det.
%
%   Run a single test.

run_test(Unit, @(Test,Line)) :-
    unit_module(Unit, Module),
    Module:'unit test'(Test, Line, TestOptions, Body),
    unit_options(Unit, UnitOptions),
    run_test(Unit, Test, Line, UnitOptions, TestOptions, Body).

%!  run_test(+Unit, +Name, +Line, +UnitOptions, +Options, +Body)
%
%   Deals with forall(Generator, Test)

run_test(Unit, Name, Line, UnitOptions, Options, Body) :-
    option(forall(Generator), Options),
    !,
    unit_module(Unit, Module),
    term_variables(Generator, Vars),
    start_test(Unit, @(Name,Line), Nth),
    State = state(0),
    call_time(forall(Module:Generator,                      % may become concurrent
                     (   incr_forall(State, I),
                         run_test_once6(Unit, Name, forall(Vars, Nth-I), Line,
                                        UnitOptions, Options, Body)
                     )),
                     Time),
    arg(1, State, Generated),
    progress(Unit, Name, Nth, forall(end, Nth, Generated), Time).
run_test(Unit, Name, Line, UnitOptions, Options, Body) :-
    start_test(Unit, @(Name,Line), Nth),
    run_test_once6(Unit, Name, Nth, Line, UnitOptions, Options, Body).

start_test(_Unit, _TestID, Nth) :-
    flag(plunit_test, Nth, Nth+1).

incr_forall(State, I) :-
    arg(1, State, I0),
    I is I0+1,
    nb_setarg(1, State, I).

%!  run_test_once6(+Unit, +Name, +Progress, +Line, +UnitOptions,
%!                 +Options, +Body)
%
%   Inherit the `timeout` and `sto` option (Global -> Unit -> Test).

run_test_once6(Unit, Name, Progress, Line, UnitOptions, Options, Body) :-
    current_test_flag(test_options, GlobalOptions),
    inherit_option(timeout, Options,  [UnitOptions, GlobalOptions], Options1),
    inherit_option(sto,     Options1, [UnitOptions, GlobalOptions], Options2),
    run_test_once(Unit, Name, Progress, Line, Options2, Body).

inherit_option(Name, Options0, Chain, Options) :-
    Term =.. [Name,_Value],
    (   option(Term, Options0)
    ->  Options = Options0
    ;   member(Opts, Chain),
        option(Term, Opts)
    ->  Options = [Term|Options0]
    ;   Options = Options0
    ).

%!  run_test_once(+Unit, +Name, Progress, +Line, +Options, +Body)
%
%   Deal with STO, i.e., running the  test multiple times with different
%   unification settings wrt. the occurs check.

run_test_once(Unit, Name, Progress, Line, Options, Body) :-
    option(sto(false), Options, false),
    !,
    current_test_flag(test_options, GlobalOptions),
    begin_test(Unit, Name, Line, Progress),
    capture_output(run_test_6(Unit, Name, Line, Options, Body, Result),
                   Output, GlobalOptions),
    end_test(Unit, Name, Line, Progress),
    report_result(Result, Progress, Output, Options).
run_test_once(Unit, Name, Progress, Line, Options, Body) :-
    current_unification_capability(Cap0),
    call_cleanup(run_test_cap(Unit, Name, Progress, Line, Options, Body),
		 set_unification_capability(Cap0)).

%!  run_test_cap(+Unit, +Name, +Progress, +Line, +Options, +Body)
%
%   Run a test in a particular STO mode or in all available STO modes.

run_test_cap(Unit, Name, Progress, Line, Options, Body) :-
    current_test_flag(test_options, GlobalOptions),
    (   option(sto(Type), Options),
        Type \== true
    ->  unification_capability(Type),
	set_unification_capability(Type),
	begin_test(Unit, Name, Line, Progress),
	capture_output(run_test_6(Unit, Name, Line, Options, Body, Result),
                       Output, GlobalOptions),
	end_test(Unit, Name, Line, Progress),
	report_result(Result, Progress, Output, Options)
    ;   findall(Key-(r(UType,Result,Output)),
                ( unification_capability(UType),
                  capture_output(test_caps(UType, Unit, Name, Progress, Line,
                                           Options, Body, Result, Key),
                                 Output, GlobalOptions)
                ),
                Pairs0),
        keysort(Pairs0, Pairs),
	group_pairs_by_key(Pairs, Keyed),
	(   Keyed == []
	->  true
	;   Keyed = [_-Results]
	->  Results = [r(_Type,Result,Output)|_],
	    report_result(Result, Progress, Output, Options) % consistent results
	;   pairs_values(Pairs, ResultByType),
	    report_result(sto(Unit, Name, Line, ResultByType), Progress, "", Options)
	)
    ).

%!  test_caps(-Type, +Unit, +Name, Progress, +Line,
%!            +Options, +Body, -Result, -Key) is semidet.
%
%   Run the test with each defined unification capability.

test_caps(Type, Unit, Name, Progress0, Line, Options, Body, Result, Key) :-
    Progress = sto(Progress0, Type),
    set_unification_capability(Type),
    begin_test(Unit, Name, Line, Progress),
    run_test_6(Unit, Name, Line, Options, Body, Result),
    end_test(Unit, Name, Line, Progress),
    result_to_key(Result, Key),
    Key \== setup_failed.

:- det(result_to_key/2).
result_to_key(failure(_, _, _, How0, _), failure(How1)) :-
    ( How0 = succeeded(_T) -> How1 = succeeded ; How0 = How1 ).
result_to_key(success(_, _, _, Determinism, _), success(Determinism)).
result_to_key(setup_failed(_,_,_), setup_failed).

%!  report_result(+Result, +Progress, +Output, +Options) is det.

:- det(report_result/4).
report_result(Result, Progress, Output, Options) :-
    current_test_flag(test_options, GlobalOptions),
    print_test_output(Result, Output, GlobalOptions),
    report_result(Result, Progress, Options).

report_result(failure(Unit, Name, Line, How, Time), Progress, Options) :-
    !,
    failure(Unit, Name, Progress, Line, How, Time, Options).
report_result(success(Unit, Name, Line, Determinism, Time), Progress, Options) :-
    !,
    success(Unit, Name, Progress, Line, Determinism, Time, Options).
report_result(setup_failed(_Unit, _Name, _Line), _Progress, _Options).
report_result(sto(Unit, Name, Line, ResultByType), Progress, Options) :-
    assert(sto(Unit, Name, Line, ResultByType)),
    print_message(error, plunit(sto(Unit, Name, Line, Progress))),
    report_sto_results(ResultByType, Progress, Options).

report_sto_results([], _, _).
report_sto_results([r(Type,Result,Output)|T], Progress, Options) :-
    print_test_output(Result, Output, Options),
    print_message(error, plunit(sto(Type, Result))),
    report_sto_results(T, Progress, Options).

print_test_output(Result, Output, Options) :-
    Output \== "",
    option(output(on_failure), Options),
    print_output(Result, Level),
    !,
    print_message(debug, plunit(test_output(Level, Output))).
print_test_output(_, _, _).

print_output(success(Unit, Name, Line, _Determinism, _Time), error) :-
    !,
    failed_assertion(Unit, Name, Line, _,_,_,_).
print_output(_, informational).


%!  run_test_6(+Unit, +Name, +Line, +Options, :Body, -Result) is det.
%
%   6th step  of the  tests.  Deals  with tests  that must  be ignored
%   (blocked, conditions fails), setup and cleanup at the test level.
%   Result is one of:
%
%     - failure(Unit, Name, Line, How, Time)
%       How is one of:
%       - succeeded
%       - Exception
%       - time_limit_exceeded(Limit)
%       - cmp_error(Cmp, E)
%       - wrong_answer(Cmp)
%       - failed
%       - no_exception
%       - wrong_error(Expect, E)
%       - wrong_answer(Expected, Bindings)
%     - success(Unit, Name, Line, Determinism, Time)
%     - setup_failed(Unit, Name, Line)

run_test_6(Unit, Name, Line, Options, Body, Result) :-
    option(setup(_Setup), Options),
    !,
    (   unit_module(Unit, Module),
        setup(Module, test(Unit,Name,Line), Options)
    ->  run_test_7(Unit, Name, Line, Options, Body, Result),
        cleanup(Module, Options)
    ;   Result = setup_failed(Unit, Name, Line)
    ).
run_test_6(Unit, Name, Line, Options, Body, Result) :-
    unit_module(Unit, Module),
    run_test_7(Unit, Name, Line, Options, Body, Result),
    cleanup(Module, Options).

%!  run_test_7(+Unit, +Name, +Line, +Options, :Body, -Result) is det.
%
%   This step  deals with the expected  outcome of the test.   It runs
%   the  actual test  and then  compares  the result  to the  outcome.
%   There are  two main categories:  dealing with a single  result and
%   all results.

run_test_7(Unit, Name, Line, Options, Body, Result) :-
    option(true(Cmp), Options),			   % expected success
    !,
    unit_module(Unit, Module),
    call_time(reify_tmo(call_det(Module:Body, Det), Result0, Options), Time),
    (   Result0 == true
    ->  (   catch(Module:Cmp, E, true)
        ->  (  var(E)
            ->  Result = success(Unit, Name, Line, Det, Time)
            ;   Result = failure(Unit, Name, Line, cmp_error(Cmp, E), Time)
            )
        ;   Result = failure(Unit, Name, Line, wrong_answer(Cmp), Time)
        )
    ;   Result0 == false
    ->  Result = failure(Unit, Name, Line, failed, Time)
    ;   Result0 = throw(E2)
    ->  Result = failure(Unit, Name, Line, E2, Time)
    ).
run_test_7(Unit, Name, Line, Options, Body, Result) :-
    option(fail, Options),                         % expected failure
    !,
    unit_module(Unit, Module),
    call_time(reify_tmo(Module:Body, Result0, Options), Time),
    (   Result0 == true
    ->  Result = failure(Unit, Name, Line, succeeded, Time)
    ;   Result0 == false
    ->  Result = success(Unit, Name, Line, true, Time)
    ;   Result0 = throw(E)
    ->  Result = failure(Unit, Name, Line, E, Time)
    ).
run_test_7(Unit, Name, Line, Options, Body, Result) :-
    option(throws(Expect), Options),		   % Expected error
    !,
    unit_module(Unit, Module),
    call_time(reify_tmo(Module:Body, Result0, Options), Time),
    (   Result0 == true
    ->  Result = failure(Unit, Name, Line, no_exception, Time)
    ;   Result0 == false
    ->  Result = failure(Unit, Name, Line, failed, Time)
    ;   Result0 = throw(E)
    ->  (   match_error(Expect, E)
        ->  Result = success(Unit, Name, Line, true, Time)
        ;   Result = failure(Unit, Name, Line, wrong_error(Expect, E), Time)
        )
    ).
run_test_7(Unit, Name, Line, Options, Body, Result) :-
    option(all(Answer), Options),                  % all(Bindings)
    !,
    nondet_test(all(Answer), Unit, Name, Line, Options, Body, Result).
run_test_7(Unit, Name, Line, Options, Body, Result) :-
    option(set(Answer), Options),                  % set(Bindings)
    !,
    nondet_test(set(Answer), Unit, Name, Line, Options, Body, Result).


%!  non_det_test(+Expected, +Unit, +Name, +Line, +Options, +Body, -Result)
%
%   Run tests on non-deterministic predicates.

nondet_test(Expected, Unit, Name, Line, Options, Body, Result) :-
    unit_module(Unit, Module),
    result_vars(Expected, Vars),
    (   call_time(reify_tmo(findall(Vars, Module:Body, Bindings),
                            Result0, Options), Time)
    ->  (   Result0 == true
        ->  (   nondet_compare(Expected, Bindings, Unit, Name, Line)
            ->  Result = success(Unit, Name, Line, true, Time)
            ;   Result = failure(Unit, Name, Line, wrong_answer(Expected, Bindings), Time)
            )
        ;   Result0 = throw(E)
        ->  Result = failure(Unit, Name, Line, E, Time)
        )
    ).

%!  result_vars(+Expected, -Vars) is det.
%
%   Create a term v(V1, ...) containing all variables at the left
%   side of the comparison operator on Expected.

result_vars(Expected, Vars) :-
    arg(1, Expected, CmpOp),
    arg(1, CmpOp, Vars).

%!  nondet_compare(+Expected, +Bindings, +Unit, +Name, +Line) is semidet.
%
%   Compare list/set results for non-deterministic predicates.
%
%   @tbd    Properly report errors
%   @bug    Sort should deal with equivalence on the comparison
%           operator.

nondet_compare(all(Cmp), Bindings, _Unit, _Name, _Line) :-
    cmp(Cmp, _Vars, Op, Values),
    cmp_list(Values, Bindings, Op).
nondet_compare(set(Cmp), Bindings0, _Unit, _Name, _Line) :-
    cmp(Cmp, _Vars, Op, Values0),
    sort(Bindings0, Bindings),
    sort(Values0, Values),
    cmp_list(Values, Bindings, Op).

cmp_list([], [], _Op).
cmp_list([E0|ET], [V0|VT], Op) :-
    call(Op, E0, V0),
    cmp_list(ET, VT, Op).

%!  cmp(+CmpTerm, -Left, -Op, -Right) is det.

cmp(Var  == Value, Var,  ==, Value).
cmp(Var =:= Value, Var, =:=, Value).
cmp(Var  =  Value, Var,  =,  Value).
:- if(swi).
cmp(Var =@= Value, Var, =@=, Value).
:- else.
:- if(sicstus).
cmp(Var =@= Value, Var, variant, Value). % variant/2 is the same =@=
:- endif.
:- endif.


%!  call_det(:Goal, -Det) is nondet.
%
%   True if Goal succeeded.  Det is unified to =true= if Goal left
%   no choicepoints and =false= otherwise.

:- if((swi;sicstus)).
call_det(Goal, Det) :-
    call_cleanup(Goal,Det0=true),
    ( var(Det0) -> Det = false ; Det = true ).
:- else.
call_det(Goal, true) :-
    call(Goal).
:- endif.

%!  match_error(+Expected, +Received) is semidet.
%
%   True if the Received errors matches the expected error. Matching
%   is based on subsumes_term/2.

match_error(Expect, Rec) :-
    subsumes_term(Expect, Rec).

%!  setup(+Module, +Context, +Options) is semidet.
%
%   Call the setup handler and  fail  if   it  cannot  run  for some
%   reason. The condition handler is  similar,   but  failing is not
%   considered an error.  Context is one of
%
%    - unit(Unit)
%      If it is the setup handler for a unit
%    - test(Unit,Name,Line)
%      If it is the setup handler for a test

setup(Module, Context, Options) :-
    option(setup(Setup), Options),
    !,
    current_test_flag(test_options, GlobalOptions),
    capture_output(reify(call_ex(Module, Setup), Result),
		   Output, GlobalOptions),
    (   Result == true
    ->  true
    ;   print_message(error,
		      plunit(error(setup, Context, Output, Result))),
	fail
    ).
setup(_,_,_).

%!  condition(+Module, +Context, +Options) is semidet.
%
%   Evaluate the test or test unit condition.

condition(Module, Context, Options) :-
    option(condition(Cond), Options),
    !,
    current_test_flag(test_options, GlobalOptions),
    capture_output(reify(call_ex(Module, Cond), Result),
		   Output, GlobalOptions),
    (   Result == true
    ->  true
    ;   Result == false
    ->  fail
    ;   print_message(error,
		      plunit(error(condition, Context, Output, Result))),
	fail
    ).
condition(_, _, _).


%!  call_ex(+Module, +Goal)
%
%   Call Goal in Module after applying goal expansion.

call_ex(Module, Goal) :-
    Module:(expand_goal(Goal, GoalEx),
	    GoalEx).

%!  cleanup(+Module, +Options) is det.
%
%   Call the cleanup handler and succeed.   Failure  or error of the
%   cleanup handler is reported, but tests continue normally.

cleanup(Module, Options) :-
    option(cleanup(Cleanup), Options, true),
    (   catch(call_ex(Module, Cleanup), E, true)
    ->  (   var(E)
	->  true
	;   print_message(warning, E)
	)
    ;   print_message(warning, goal_failed(Cleanup, '(cleanup handler)'))
    ).

success(Unit, Name, Progress, Line, Det, Time, Options) :-
    memberchk(fixme(Reason), Options),
    !,
    (   (   Det == true
	;   memberchk(nondet, Options)
	)
    ->  progress(Unit, Name, Progress, fixme(passed), Time),
	Ok = passed
    ;   progress(Unit, Name, Progress, fixme(nondet), Time),
	Ok = nondet
    ),
    flush_output(user_error),
    assert(fixme(Unit, Name, Line, Reason, Ok)).
success(Unit, Name, Progress, Line, _, Time, Options) :-
    failed_assertion(Unit, Name, Line, _,_,_,_),
    !,
    failure(Unit, Name, Progress, Line, assertion, Time, Options).
success(Unit, Name, Progress, Line, Det, Time, Options) :-
    assert(passed(Unit, Name, Line, Det, Time)),
    (   (   Det == true
	;   memberchk(nondet, Options)
	)
    ->  progress(Unit, Name, Progress, passed, Time)
    ;   unit_file(Unit, File),
	print_message(warning, plunit(nondet(File, Line, Name)))
    ).

%!  failure(+Unit, +Name, +Progress, +Line, +How, +Time, +Options) is det.
%
%   Test failed.  Report the error.

failure(Unit, Name, Progress, Line, _, Time, Options),
  memberchk(fixme(Reason), Options) =>
    progress(Unit, Name, Progress, fixme(failed), Time),
    assert(fixme(Unit, Name, Line, Reason, failed)).
failure(Unit, Name, Progress, Line, time_limit_exceeded(Limit), Time, Options) =>
    report_failure(Unit, Name, Progress, Line, timeout(Limit), Time, Options),
    progress(Unit, Name, Progress, timeout(Limit), Time),
    assert_cyclic(timeout(Unit, Name, Line, Limit, Time)).
failure(Unit, Name, Progress, Line, E, Time, Options) =>
    report_failure(Unit, Name, Progress, Line, E, Time, Options),
    progress(Unit, Name, Progress, failed, Time),
    assert_cyclic(failed(Unit, Name, Line, E, Time)).

%!  assert_cyclic(+Term) is det.
%
%   Assert  a  possibly  cyclic  unit   clause.  Current  SWI-Prolog
%   assert/1 does not handle cyclic terms,  so we emulate this using
%   the recorded database.
%
%   @tbd    Implement cycle-safe assert and remove this.

:- if(swi).
assert_cyclic(Term) :-
    acyclic_term(Term),
    !,
    assert(Term).
assert_cyclic(Term) :-
    Term =.. [Functor|Args],
    recorda(cyclic, Args, Id),
    functor(Term, _, Arity),
    length(NewArgs, Arity),
    Head =.. [Functor|NewArgs],
    assert((Head :- recorded(_, Var, Id), Var = NewArgs)).
:- else.
:- if(sicstus).
:- endif.
assert_cyclic(Term) :-
    assert(Term).
:- endif.


		 /*******************************
		 *             JOBS             *
		 *******************************/

:- if(current_prolog_flag(threads, true)).

:- dynamic
       job_data/2,		% Queue, Threads
       scheduled_unit/1.

schedule_unit(_:[]) :-
    !.
schedule_unit(UnitAndTests) :-
    UnitAndTests = Unit:_Tests,
    job_data(Queue, _),
    !,
    assertz(scheduled_unit(Unit)),
    thread_send_message(Queue, unit(UnitAndTests)).
schedule_unit(Unit) :-
    run_unit(Unit).

%!  setup_jobs(+Count) is det.
%
%   Setup threads for concurrent testing.

setup_jobs(Count) :-
    current_prolog_flag(cpu_count, Cores),
    current_test_flag(test_options, Options),
    option(concurrent(true), Options),
    option(jobs(Jobs0), Options, Cores),
    Jobs is min(Count, Jobs0),
    Jobs > 1,
    !,
    message_queue_create(Q, [alias(plunit_jobs)]),
    length(TIDs, Jobs),
    foldl(create_plunit_job(Q), TIDs, 1, _),
    asserta(job_data(Q, TIDs)),
    print_message(silent, plunit(jobs(Jobs))).
setup_jobs(_) :-
    print_message(silent, plunit(jobs(1))).

create_plunit_job(Q, TID, N, N1) :-
    N1 is N + 1,
    atom_concat(plunit_job_, N, Alias),
    thread_create(plunit_job(Q), TID, [alias(Alias)]).

plunit_job(Queue) :-
    repeat,
    (   catch(thread_get_message(Queue, Job), error(_,_), fail)
    ->  job(Job),
	fail
    ;   !
    ).

job(unit(Unit:Tests)) =>
    run_unit(Unit:Tests).

cleanup_jobs :-
    retract(job_data(Queue, TIDSs)),
    !,
    message_queue_destroy(Queue),
    maplist(thread_join, TIDSs).
cleanup_jobs.

%!  job_wait is det.
%
%   Wait for all test jobs to finish.

job_wait :-
    thread_wait(\+ scheduled_unit(_),
		[ wait_preds([scheduled_unit/1])
		]).

job_info(begin(unit(_Unit))) =>
    true.
job_info(end(unit(Unit, _Summary))) =>
    retractall(scheduled_unit(Unit)).

:- else.			% No jobs

schedule_unit(Unit) :-
    run_unit(Unit).

setup_jobs(_) :-
    print_message(silent, plunit(jobs(1))).
cleanup_jobs.
job_wait.
job_info(_).

:- endif.



		 /*******************************
		 *            REPORTING         *
		 *******************************/

%!  begin_test(+Unit, +Test, +Line, +Progress) is det.
%!  end_test(+Unit, +Test, +Line, +Progress) is det.
%
%   Maintain running/5 and report a test has started/is ended using
%   a =silent= message:
%
%       * plunit(begin(Unit:Test, File:Line, Progress))
%       * plunit(end(Unit:Test, File:Line, Progress))
%
%   @see message_hook/3 for intercepting these messages

begin_test(Unit, Test, Line, Progress) :-
    thread_self(Me),
    assert(running(Unit, Test, Line, Progress, Me)),
    unit_file(Unit, File),
    test_count(Total),
    print_message(silent, plunit(begin(Unit:Test, File:Line, Progress/Total))).

end_test(Unit, Test, Line, Progress) :-
    thread_self(Me),
    retractall(running(_,_,_,_,Me)),
    unit_file(Unit, File),
    test_count(Total),
    print_message(silent, plunit(end(Unit:Test, File:Line, Progress/Total))).

%!  running_tests is det.
%
%   Print the currently running test.

running_tests :-
    running_tests(Running),
    print_message(informational, plunit(running(Running))).

running_tests(Running) :-
    findall(running(Unit:Test, File:Line, STO, Thread),
	    (   running(Unit, Test, Line, STO, Thread),
		unit_file(Unit, File)
	    ), Running).


%!  current_test(?Unit, ?Test, ?Line, ?Body, ?Options) is nondet.
%
%   True when a test with the specified properties is loaded.

current_test(Unit, Test, Line, Body, Options) :-
    current_unit(Unit, Module, _Supers, _UnitOptions),
    Module:'unit test'(Test, Line, Options, Body).

%!  current_test_unit(?Unit, ?Options) is nondet.
%
%   True when a Unit is a current unit test declared with Options.

current_test_unit(Unit, UnitOptions) :-
    current_unit(Unit, _Module, _Supers, UnitOptions).


count(Goal, Count) :-
    aggregate_all(count, Goal, Count).

%!  test_summary(?Unit, -Summary) is det.
%
%   True if there are no failures, otherwise false.

test_summary(Unit, Summary) :-
    count(failed(Unit, _0Test, _0Line, _Reason, _0Time), Failed),
    count(timeout(Unit, _0Test, _0Line, _Limit, _0Time), Timeout),
    count(failed_assertion(Unit, _0Test, _0Line,
			   _ALoc, _STO, _0Reason, _Goal), FailedAssertion),
    count(sto(Unit, _0Test, _0Line, _Results), STO),
    count(passed(Unit, _0Test, _0Line, _Det, _0Time), Passed),
    count(blocked(Unit, _0Test, _0Line, _0Reason), Blocked),
    Summary = plunit{passed:Passed,
		     failed:Failed,
		     failed_assertions:FailedAssertion,
		     timeout:Timeout,
		     blocked:Blocked,
		     sto:STO}.

%!  all_tests_passed(?Unit) is semidet.
%
%   True if Unit passed. If Unit is unbound   this  is true if all units
%   passed.

all_tests_passed(Unit) :-
    test_summary(Unit, Summary),
    test_summary_passed(Summary).

test_summary_passed(Summary) :-
    _{failed: 0, failed_assertions: 0, sto: 0} :< Summary.

%!  report is det.
%
%   Print a summary of the tests that ran.

report :-
    test_summary(_, Summary),
    print_message(silent, plunit(Summary)),
    _{ passed:Passed,
       failed:Failed,
       failed_assertions:_FailedAssertion,
       timeout:Timeout,
       blocked:Blocked,
       sto:STO
     } :< Summary,
    (   Passed+Failed+Timeout+Blocked+STO =:= 0
    ->  info(plunit(no_tests))
    ;   Failed+Timeout+Blocked+STO =:= 0
    ->  report_fixme,
        test_count(Total),
	info(plunit(all_passed(Total, Passed)))
    ;   report_blocked(Blocked),
	report_fixme,
	report_failed(Failed),
	report_sto(STO),
	report_timeout(Timeout),
	info(plunit(passed(Passed)))
    ).

report_blocked(0) =>
    true.
report_blocked(Blocked) =>
    info(plunit(blocked(Blocked))),
    (   blocked(Unit, Name, Line, Reason),
	unit_file(Unit, File),
	print_message(informational,
		      plunit(blocked(File:Line, Name, Reason))),
	fail ; true
    ).

report_failed(Failed) :-
    print_message(error, plunit(failed(Failed))).

report_timeout(Count) :-
    print_message(warning, plunit(timeout(Count))).

report_sto(STO) :-
    print_message(error, plunit(sto(STO))).

report_fixme :-
    report_fixme(_,_,_).

report_fixme(TuplesF, TuplesP, TuplesN) :-
    fixme(failed, TuplesF, Failed),
    fixme(passed, TuplesP, Passed),
    fixme(nondet, TuplesN, Nondet),
    print_message(informational, plunit(fixme(Failed, Passed, Nondet))).


fixme(How, Tuples, Count) :-
    findall(fixme(Unit, Name, Line, Reason, How),
	    fixme(Unit, Name, Line, Reason, How), Tuples),
    length(Tuples, Count).


report_failure(Unit, Name, Progress, _, assertion, Time, _) =>
    progress(Unit, Name, Progress, assertion, Time).
report_failure(Unit, Name, Progress, Line, timeout(Limit), _Time, _Options) =>
    print_message(warning, plunit(timeout(Unit, Name, Progress, Line, Limit))).
report_failure(Unit, Name, Progress, Line, Error, _Time, _Options) =>
    print_message(error, plunit(failed(Unit, Name, Progress, Line, Error))).


%!  test_report(+What) is det.
%
%   Produce reports on test  results  after   the  run.  Currently  only
%   supports `fixme` for What.

test_report(fixme) :-
    !,
    report_fixme(TuplesF, TuplesP, TuplesN),
    append([TuplesF, TuplesP, TuplesN], Tuples),
    print_message(informational, plunit(fixme(Tuples))).
test_report(What) :-
    throw_error(domain_error(report_class, What), _).


		 /*******************************
		 *             INFO             *
		 *******************************/

%!  current_test_set(?Unit) is nondet.
%
%   True if Unit is a currently loaded test-set.

current_test_set(Unit) :-
    current_unit(Unit, _Module, _Context, _Options).

%!  unit_file(+Unit, -File) is det.
%!  unit_file(-Unit, +File) is nondet.

unit_file(Unit, File) :-
    current_unit(Unit, Module, _Context, _Options),
    current_module(Module, File).
unit_file(Unit, PlFile) :-
    nonvar(PlFile),
    test_file_for(TestFile, PlFile),
    current_module(Module, TestFile),
    current_unit(Unit, Module, _Context, _Options).


		 /*******************************
		 *             FILES            *
		 *******************************/

%!  load_test_files(+Options) is det.
%
%   Load .plt test-files related to loaded source-files.

load_test_files(_Options) :-
    (   source_file(File),
	file_name_extension(Base, Old, File),
	Old \== plt,
	file_name_extension(Base, plt, TestFile),
	exists_file(TestFile),
	(   test_file_for(TestFile, File)
	->  true
	;   load_files(TestFile,
		       [ if(changed),
			 imports([])
		       ]),
	    asserta(test_file_for(TestFile, File))
	),
	fail ; true
    ).



		 /*******************************
		 *           MESSAGES           *
		 *******************************/

%!  info(+Term)
%
%   Runs print_message(Level, Term), where Level is   one of `silent` or
%   `informational` (default).

info(Term) :-
    message_level(Level),
    print_message(Level, Term).

%!  progress(+Unit, +Name, +Progress, +Result, +Time) is det.
%
%   Test Unit:Name completed in Time. Result is the result and is one of
%
%     - passed
%     - failed
%     - assertion
%     - nondet
%     - fixme(passed)
%     - fixme(nondet)
%     - fixme(failed)
%     - forall(end, Nth, FTotal)
%       Pseudo result for completion of a forall(Gen,Test) set.  Mapped
%       to forall(FTotal, FFailed)

progress(Unit, Name, _Progress, forall(end, Nth, FTotal), Time) =>
    (   retract(forall_failures(Nth, FFailed))
    ->  true
    ;   FFailed = 0
    ),
    test_count(Total),
    print_message(information, plunit(progress(Unit, Name, forall(FTotal,FFailed), Nth/Total, Time))).
progress(Unit, Name, Progress, Result, Time), Progress = forall(_Vars, Nth-_I) =>
    with_mutex(plunit_forall_counter,
               update_forall_failures(Nth, Result)),
    test_count(Total),
    print_message(information, plunit(progress(Unit, Name, Result, Progress/Total, Time))).
progress(Unit, Name, Progress, Result, Time) =>
    test_count(Total),
    print_message(information, plunit(progress(Unit, Name, Result, Progress/Total, Time))).

update_forall_failures(_Nth, passed) =>
    true.
update_forall_failures(Nth, _) =>
    (   retract(forall_failures(Nth, Failed0))
    ->  true
    ;   Failed0 = 0
    ),
    Failed is Failed0+1,
    asserta(forall_failures(Nth, Failed)).

message_level(Level) :-
    current_test_flag(test_options, Options),
    option(silent(Silent), Options, false),
    (   Silent == false
    ->  Level = informational
    ;   Level = silent
    ).

locationprefix(File:Line) -->
    !,
    [ url(File:Line), ':\n\t' ].
locationprefix(test(Unit,_Test,Line)) -->
    !,
    { unit_file(Unit, File) },
    locationprefix(File:Line).
locationprefix(unit(Unit)) -->
    !,
    [ 'PL-Unit: unit ~w: '-[Unit] ].
locationprefix(FileLine) -->
    { throw_error(type_error(locationprefix,FileLine), _) }.

:- discontiguous
    message//1.
:- '$hide'(message//1).

message(error(context_error(plunit_close(Name, -)), _)) -->
    [ 'PL-Unit: cannot close unit ~w: no open unit'-[Name] ].
message(error(context_error(plunit_close(Name, Start)), _)) -->
    [ 'PL-Unit: cannot close unit ~w: current unit is ~w'-[Name, Start] ].
message(plunit(nondet(File, Line, Name))) -->
    locationprefix(File:Line),
    [ 'PL-Unit: Test ~w: Test succeeded with choicepoint'- [Name] ].
message(error(plunit(incompatible_options, Tests), _)) -->
    [ 'PL-Unit: incompatible test-options: ~p'-[Tests] ].

					% Unit start/end
:- if(swi).
message(plunit(progress(_Unit, _Name, Result, _N_T, _Time))) -->
    [ at_same_line ], result(Result), [flush].
message(plunit(begin(Unit))) -->
    [ 'PL-Unit: ~w '-[Unit], flush ].
message(plunit(end(_Unit, Summary))) -->
    [ at_same_line ],
    (   {test_summary_passed(Summary)}
    ->  [ ' passed' ]
    ;   [ ansi(error, '**FAILED', []) ]
    ),
    [ ' ~3f sec'-[Summary.time.cpu] ].
:- else.
message(plunit(begin(Unit))) -->
    [ 'PL-Unit: ~w '-[Unit]/*, flush-[]*/ ].
message(plunit(end(_Unit, _Summary))) -->
    [ ' done'-[] ].
:- endif.
message(plunit(blocked(unit(Unit, Reason)))) -->
    [ 'PL-Unit: ~w blocked: ~w'-[Unit, Reason] ].
message(plunit(running([]))) -->
    !,
    [ 'PL-Unit: no tests running' ].
message(plunit(running([One]))) -->
    !,
    [ 'PL-Unit: running ' ],
    running(One).
message(plunit(running(More))) -->
    !,
    [ 'PL-Unit: running tests:', nl ],
    running(More).
message(plunit(fixme([]))) --> !.
message(plunit(fixme(Tuples))) -->
    !,
    fixme_message(Tuples).

					% Blocked tests
message(plunit(blocked(1))) -->
    !,
    [ 'one test is blocked:'-[] ].
message(plunit(blocked(N))) -->
    [ '~D tests are blocked:'-[N] ].
message(plunit(blocked(Pos, Name, Reason))) -->
    locationprefix(Pos),
    test_name(Name, -),
    [ ': ~w'-[Reason] ].

					% fail/success
message(plunit(no_tests)) -->
    !,
    [ 'No tests to run' ].
message(plunit(all_passed(1, 1))) -->
    !,
    [ 'test passed' ].
message(plunit(all_passed(Total, Total))) -->
    !,
    [ 'All ~D tests passed'-[Total] ].
message(plunit(all_passed(Total, Count))) -->
    !,
    { SubTests is Count-Total },
    [ 'All ~D (+~D sub-tests) tests passed'-[Total, SubTests] ].
message(plunit(passed(Count))) -->
    !,
    [ '~D tests passed'-[Count] ].
message(plunit(failed(0))) -->
    !,
    [].
message(plunit(failed(1))) -->
    !,
    [ '1 test failed'-[] ].
message(plunit(failed(N))) -->
    [ '~D tests failed'-[N] ].
message(plunit(failed_assertions(0))) -->
    !,
    [].
message(plunit(failed_assertions(1))) -->
    !,
    [ '1 assertion failed'-[] ].
message(plunit(failed_assertions(N))) -->
    [ '~D assertions failed'-[N] ].
message(plunit(sto(0))) -->
    !,
    [].
message(plunit(sto(N))) -->
    [ '~D test results depend on unification mode'-[N] ].
message(plunit(timeout(0))) -->
    !,
    [].
message(plunit(timeout(N))) -->
    [ '~D tests timed out'-[N] ].
message(plunit(fixme(0,0,0))) -->
    [].
message(plunit(fixme(Failed,0,0))) -->
    !,
    [ 'all ~D tests flagged FIXME failed'-[Failed] ].
message(plunit(fixme(Failed,Passed,0))) -->
    [ 'FIXME: ~D failed; ~D passed'-[Failed, Passed] ].
message(plunit(fixme(Failed,Passed,Nondet))) -->
    { TotalPassed is Passed+Nondet },
    [ 'FIXME: ~D failed; ~D passed; (~D nondet)'-
      [Failed, TotalPassed, Nondet] ].
message(plunit(failed(Unit, Name, Progress, Line, Failure))) -->
    { unit_file(Unit, File) },
    locationprefix(File:Line),
    test_name(Name, Progress),
    [': '-[] ],
    failure(Failure).
message(plunit(timeout(Unit, Name, Progress, Line, Limit))) -->
    { unit_file(Unit, File) },
    locationprefix(File:Line),
    test_name(Name, Progress),
    [': '-[] ],
    timeout(Limit).
:- if(swi).
message(plunit(failed_assertion(Unit, Name, Line, AssertLoc,
				Progress, Reason, Goal))) -->
    { unit_file(Unit, File) },
    locationprefix(File:Line),
    test_name(Name, Progress),
    [ ': assertion'-[] ],
    assertion_location(AssertLoc, File),
    assertion_reason(Reason), ['\n\t'],
    assertion_goal(Unit, Goal).

assertion_location(File:Line, File) -->
    [ ' at line ~w'-[Line] ].
assertion_location(File:Line, _) -->
    [ ' at ', url(File:Line) ].
assertion_location(unknown, _) -->
    [].

assertion_reason(fail) -->
    !,
    [ ' failed'-[] ].
assertion_reason(Error) -->
    { message_to_string(Error, String) },
    [ ' raised "~w"'-[String] ].

assertion_goal(Unit, Goal) -->
    { unit_module(Unit, Module),
      unqualify(Goal, Module, Plain)
    },
    [ 'Assertion: ~p'-[Plain] ].

unqualify(Var, _, Var) :-
    var(Var),
    !.
unqualify(M:Goal, Unit, Goal) :-
    nonvar(M),
    unit_module(Unit, M),
    !.
unqualify(M:Goal, _, Goal) :-
    callable(Goal),
    predicate_property(M:Goal, imported_from(system)),
    !.
unqualify(Goal, _, Goal).

result(passed)        --> ['.'-[]].
result(nondet)        --> ['+'-[]].
result(fixme(passed)) --> ['*'-[]].
result(fixme(failed)) --> ['!'-[]].
result(failed)        --> ['-'-[]].
result(timeout(_Lim)) --> ['T'-[]].
result(assertion)     --> ['A'-[]].
result(forall(_,_))   --> [].

:- endif.
					% Setup/condition errors
message(plunit(error(Where, Context, _Output, throw(Exception)))) -->
    locationprefix(Context),
    { message_to_string(Exception, String) },
    [ 'error in ~w: ~w'-[Where, String] ].
message(plunit(error(Where, Context, _Output, false))) -->
    locationprefix(Context),
    [ 'setup failed in ~w'-[Where] ].

					% STO messages
message(plunit(sto(Unit, Name, Line, Progress))) -->
    { unit_file(Unit, File) },
    locationprefix(File:Line),
    test_name(Name, Progress),
    [' is subject to occurs check (STO): '-[] ].
message(plunit(sto(Type, Result))) -->
    sto_type(Type),
    sto_result(Result).

                                        % delayed output
message(plunit(test_output(_, Output))) -->
    [ '~s'-[Output] ].
					% Interrupts (SWI)
:- if(swi).
message(interrupt(begin)) -->
    { thread_self(Me),
      running(Unit, Test, Line, STO, Me),
      !,
      unit_file(Unit, File)
    },
    [ 'Interrupted test '-[] ],
    running(running(Unit:Test, File:Line, STO, Me)),
    [nl],
    '$messages':prolog_message(interrupt(begin)).
message(interrupt(begin)) -->
    '$messages':prolog_message(interrupt(begin)).
:- endif.

test_name(Name, forall(Bindings, _Nth-I)) -->
    !,
    [ 'test ~w (~d-th forall bindings = ~p)'-[Name, I, Bindings] ].
test_name(Name, _) -->
    !,
    [ 'test ~w'-[Name] ].

sto_type(sto_error_incomplete) -->
    [ 'Finite trees (error checking): ' ].
sto_type(rational_trees) -->
    [ 'Rational trees: ' ].
sto_type(finite_trees) -->
    [ 'Finite trees: ' ].

sto_result(success(_Unit, _Name, _Line, Det, Time)) -->
    det(Det),
    [ ' success in ~3f seconds'-[Time.cpu] ].
sto_result(failure(_Unit, _Name, _Line, How, _Time)) -->
    failure(How).

det(true) -->
    [ 'deterministic' ].
det(false) -->
    [ 'non-deterministic' ].

running(running(Unit:Test, File:Line, STO, Thread)) -->
    thread(Thread),
    [ '~q:~q at '-[Unit, Test], url(File:Line) ],
    current_sto(STO).
running([H|T]) -->
    ['\t'], running(H),
    (   {T == []}
    ->  []
    ;   [nl], running(T)
    ).

thread(main) --> !.
thread(Other) -->
    [' [~w] '-[Other] ].

current_sto(sto_error_incomplete) -->
    [ ' (STO: error checking)' ].
current_sto(rational_trees) -->
    [].
current_sto(finite_trees) -->
    [ ' (STO: occurs check enabled)' ].

:- if(swi).
write_term(T, OPS) -->
    ['~@'-[write_term(T,OPS)]].
:- else.
write_term(T, _OPS) -->
    ['~q'-[T]].
:- endif.

expected_got_ops_(Ex, E, OPS, Goals) -->
    ['    Expected: '-[]], write_term(Ex, OPS), [nl],
    ['    Got:      '-[]], write_term(E,  OPS), [nl],
    ( { Goals = [] } -> []
    ; ['       with: '-[]], write_term(Goals, OPS), [nl]
    ).


failure(Var) -->
    { var(Var) },
    !,
    [ 'Unknown failure?' ].
failure(succeeded(Time)) -->
    !,
    [ 'must fail but succeeded in ~2f seconds~n'-[Time] ].
failure(wrong_error(Expected, Error)) -->
    !,
    { copy_term(Expected-Error, Ex-E, Goals),
      numbervars(Ex-E-Goals, 0, _),
      write_options(OPS)
    },
    [ 'wrong error'-[], nl ],
    expected_got_ops_(Ex, E, OPS, Goals).
failure(wrong_answer(Cmp)) -->
    { Cmp =.. [Op,Answer,Expected],
      !,
      copy_term(Expected-Answer, Ex-A, Goals),
      numbervars(Ex-A-Goals, 0, _),
      write_options(OPS)
    },
    [ 'wrong answer (compared using ~w)'-[Op], nl ],
    expected_got_ops_(Ex, A, OPS, Goals).
failure(wrong_answer(CmpExpected, Bindings)) -->
    { (   CmpExpected = all(Cmp)
      ->  Cmp =.. [_Op1,_,Expected],
	  Got = Bindings,
	  Type = all
      ;   CmpExpected = set(Cmp),
	  Cmp =.. [_Op2,_,Expected0],
	  sort(Expected0, Expected),
	  sort(Bindings, Got),
	  Type = set
      )
    },
    [ 'wrong "~w" answer:'-[Type] ],
    [ nl, '    Expected: ~q'-[Expected] ],
    [ nl, '       Found: ~q'-[Got] ].
:- if(swi).
failure(cmp_error(_Cmp, Error)) -->
    { message_to_string(Error, Message) },
    [ 'Comparison error: ~w'-[Message] ].
failure(Error) -->
    { Error = error(_,_),
      !,
      message_to_string(Error, Message)
    },
    [ 'received error: ~w'-[Message] ].
:- endif.
failure(Why) -->
    [ '~p'-[Why] ].

timeout(Limit) -->
    [ 'Timeout exceeeded (~2f sec)'-[Limit] ].

fixme_message([]) --> [].
fixme_message([fixme(Unit, _Name, Line, Reason, How)|T]) -->
    { unit_file(Unit, File) },
    fixme_message(File:Line, Reason, How),
    (   {T == []}
    ->  []
    ;   [nl],
	fixme_message(T)
    ).

fixme_message(Location, Reason, failed) -->
    [ 'FIXME: ~w: ~w'-[Location, Reason] ].
fixme_message(Location, Reason, passed) -->
    [ 'FIXME: ~w: passed ~w'-[Location, Reason] ].
fixme_message(Location, Reason, nondet) -->
    [ 'FIXME: ~w: passed (nondet) ~w'-[Location, Reason] ].


write_options([ numbervars(true),
		quoted(true),
		portray(true),
		max_depth(100),
		attributes(portray)
	      ]).

:- if(swi).

:- multifile
    prolog:message/3,
    user:message_hook/3.

prolog:message(Term) -->
    message(Term).

%       user:message_hook(+Term, +Kind, +Lines)

user:message_hook(make(done(Files)), _, _) :-
    make_run_tests(Files),
    fail.                           % give other hooks a chance

:- endif.

:- if(sicstus).

user:generate_message_hook(Message) -->
    message(Message),
    [nl].                           % SICStus requires nl at the end

%!  user:message_hook(+Severity, +Message, +Lines) is semidet.
%
%   Redefine printing some messages. It appears   SICStus has no way
%   to get multiple messages at the same   line, so we roll our own.
%   As there is a lot pre-wired and   checked in the SICStus message
%   handling we cannot reuse the lines. Unless I miss something ...

user:message_hook(informational, plunit(begin(Unit)), _Lines) :-
    format(user_error, '% PL-Unit: ~w ', [Unit]),
    flush_output(user_error).
user:message_hook(informational, plunit(end(_Unit)), _Lines) :-
    format(user, ' done~n', []).

:- endif.
