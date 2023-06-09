

-module(sudoku).
%-include_lib("eqc/include/eqc.hrl").
-compile(export_all).

%% %% generators

%% matrix(M,N) ->
%%     vector(M,vector(N,nat())).

%% matrix transpose

transpose([Row]) ->
    [[X] || X <- Row];
transpose([Row|M]) ->
    [[X|Xs] || {X,Xs} <- lists:zip(Row,transpose(M))].

%% prop_transpose() ->
%%     ?FORALL({M,N},{nat(),nat()},
%% 	    ?FORALL(Mat,matrix(M+1,N+1),
%% 		    transpose(transpose(Mat)) == Mat)).

%% map a matrix to a list of 3x3 blocks, each represented by the list
%% of elements in row order

triples([A,B,C|D]) ->
    [[A,B,C]|triples(D)];
triples([]) ->
    [].

blocks(M) ->
    Blocks = [triples(X) || X <- transpose([triples(Row) || Row <- M])],
    lists:append(
      lists:map(fun(X)->
			lists:map(fun lists:append/1, X)
		end,
		Blocks)).

unblocks(M) ->
    lists:map(
      fun lists:append/1,
      transpose(
	lists:map(
	  fun lists:append/1,
	  lists:map(
	    fun(X)->lists:map(fun triples/1,X) end,
	    triples(M))))).

%% prop_blocks() ->
%%     ?FORALL(M,matrix(9,9),
%% 	    unblocks(blocks(M)) == M).

%% decide whether a position is safe

entries(Row) ->
    [X || X <- Row,
	  1 =< X andalso X =< 9].

safe_entries(Row) ->
    Entries = entries(Row),
    lists:sort(Entries) == lists:usort(Entries).

safe_rows(M) ->
    lists:all(fun safe_entries/1,M).

safe(M) ->
    safe_rows(M) andalso
	safe_rows(transpose(M)) andalso
	safe_rows(blocks(M)).

%% fill blank entries with a list of all possible values 1..9

fill(M) ->
    Nine = lists:seq(1,9),
    [[if 1=<X, X=<9 ->
	      X;
	 true ->
	      Nine
      end
      || X <- Row]
     || Row <- M].

%% refine entries which are lists by removing numbers they are known
%% not to be


refine(M) ->
    NewM =
	refine_rows(
	  transpose(
        refine_rows(
	      transpose(
		unblocks(
        refine_rows(
		    blocks(M))))))),
    if M==NewM ->
	    M;
       true ->
	    refine(NewM)
    end.

refine_rows(M) ->
    lists:map(fun refine_row/1,M).

p_refine_rows(M) ->
    pmap(fun refine_row/1,M).


%spawn_link 
%trap exit flagga på pmap 
%process_flag trap_exit 

pmap(F, L) ->
    S = self(),
    process_flag(trap_exit, true),
    Pids = lists:map(fun(I) -> spawn_link(fun() -> pmap_f(S, F, I) end) end, L),
    pmap_gather(Pids).
    
pmap_gather([H|T]) ->
    receive
        {H, {'EXIT',_, no_solution}} -> 
            kill_all(T),
            exit(no_solution);
        {H, ok} -> pmap_gather([H|T]);
        {H, Ret} -> [Ret|pmap_gather(T)]
    end;
pmap_gather([]) ->
    [].
    
pmap_f(Parent, F, I) ->
    Parent ! {self(), (catch F(I))}. 

kill_all([H|T]) -> exit(H,kill), kill_all(T);
kill_all([]) -> [].

flush()->
    receive
        _ -> flush()
    after
        0 -> ok
    end.


refine_row(Row) ->
    Entries = entries(Row),
    NewRow =
	[if is_list(X) ->
		 case X--Entries of
		     [] ->
			 exit(no_solution);
		     [Y] ->
			 Y;
		     NewX ->
			 NewX
		 end;
	    true ->
		 X
	 end
	 || X <- Row],
    NewEntries = entries(NewRow),
    %% check we didn't create a duplicate entry
    case length(lists:usort(NewEntries)) == length(NewEntries) of
	true ->
	    NewRow;
	false ->
	    exit(no_solution)
    end.

is_exit({'EXIT',_}) ->
    true;
is_exit(_) ->
    false.

%% is a puzzle solved?

solved(M) ->
    lists:all(fun solved_row/1,M).

solved_row(Row) ->
    lists:all(fun(X)-> 1=<X andalso X=<9 end, Row).

%% how hard is the puzzle?

hard(M) ->		      
    lists:sum(
      [lists:sum(
	 [if is_list(X) ->
		  length(X);
	     true ->
		  0
	  end
	  || X <- Row])
       || Row <- M]).

%% choose a position {I,J,Guesses} to guess an element, with the
%% fewest possible choices

guess(M) ->
    Nine = lists:seq(1,9),
    {_,I,J,X} =
	lists:min([{length(X),I,J,X}
		   || {I,Row} <- lists:zip(Nine,M),
		      {J,X} <- lists:zip(Nine,Row),
		      is_list(X)]),
    {I,J,X}.

%% given a matrix, guess an element to form a list of possible
%% extended matrices, easiest problem first.

guesses(M) ->
    {I,J,Guesses} = guess(M),
    Ms = [catch refine(update_element(M,I,J,G)) || G <- Guesses],
    SortedGuesses =
	lists:sort(
	  [{hard(NewM),NewM}
	   || NewM <- Ms,
	      not is_exit(NewM)]),
    [G || {_,G} <- SortedGuesses].

update_element(M,I,J,G) ->
    update_nth(I,update_nth(J,G,lists:nth(I,M)),M).

update_nth(I,X,Xs) ->
    {Pre,[_|Post]} = lists:split(I-1,Xs),
    Pre++[X|Post].

%% prop_update() ->
%%     ?FORALL(L,list(int()),
%% 	    ?IMPLIES(L/=[],
%% 		     ?FORALL(I,choose(1,length(L)),
%% 			     update_nth(I,lists:nth(I,L),L) == L))).

%% solve a puzzle

solve(M) ->
    flush(),
    %io:format("Sudoku: ~w~n", [M]),
    Solution = solve_refined(refine(fill(M))),
    case valid_solution(Solution) of
	true ->
	    Solution;
	false ->
	    exit({invalid_solution,Solution})
    end.

solve_refined(M) ->
    %io:format("Hello from: ~p~n", [self()]),
    case solved(M) of
	true ->
	    M;
	false ->
        %io:format("Matrix: ~w~n", [M]),
        G = guesses(M),
        %io:format("Guesses: ~w~n", [G]),
	    solve_one(G)
    end.

p_solve(M) ->
    flush(),
    %io:format("Sudoku: ~w~n", [M]),
    Solution = p_solve_refined(refine(fill(M)),0),
    case valid_solution(Solution) of
    true ->
        Solution;
    false ->
        exit({invalid_solution,Solution})
    end.

p_solve_refined(M,I) ->
    %io:format("Hello from: ~p~n", [self()]),
    case solved(M) of
    true ->
        M;
    false ->
        %io:format("Matrix: ~w~n", [M]),
        G = guesses(M),
        %io:format("Guesses: ~w~n", [G]),
        solve_all(G,I)
    end.


solve_all(M,2) -> solve_one(M);
solve_all([],_) -> exit(no_solution);
solve_all(M,I) -> solve_all(M,[],I).

solve_all([],Pids,_) ->
    %io:format("base \n"),
    receive_solves(Pids, 0);

solve_all([M|Ms], Pids,I) ->
    S = self(),
    %io:format("self: ~w", [S]),
    process_flag(trap_exit, true),
    Pid = spawn_link(fun() -> S ! p_solve_refined(M,I+1) end),
    %io:format("self: ~w, Pids: ~w~n", [S, Pids ++ [Pid]]),
    solve_all(Ms, Pids ++ [Pid],I).

receive_solves(Pids, I) ->
    receive
        %X -> io:format("Recieved: ~p~n",[X]);
        {'EXIT', _ , no_solution} ->
            if
               I >= length(Pids)-1 -> 
                    exit(no_solution);
                true -> 
                    receive_solves(Pids, I+1) 
            end;
        ok -> receive_solves(Pids, I);
        {_, ok} -> receive_solves(Pids, I);
        {'EXIT', _ , _ } -> receive_solves(Pids, I);

        Solution ->
            kill_all(Pids),
            flush(),
            Solution
    end.


solve_one([]) ->
    exit(no_solution);
solve_one([M]) ->
    solve_refined(M);
solve_one([M|Ms]) ->
    case catch solve_refined(M) of
    {'EXIT',no_solution} ->
        solve_one(Ms);
    Solution ->
        Solution
    end.


%% benchmarks

-define(EXECUTIONS,50).

bm(F) ->
    {T,_} = timer:tc(?MODULE,repeat,[F]),
    T/?EXECUTIONS/1000.

repeat(F) ->
    [F() || _ <- lists:seq(1,?EXECUTIONS)].

benchmarks(Puzzles) ->
    %io:format("Puzzles: ~w~n", [Puzzles]),
    [{Name,bm(fun()->p_solve(M) end)} || {Name,M} <- Puzzles].

benchmarks() ->
  {ok,Puzzles} = file:consult("problems.txt"),
  timer:tc(?MODULE,benchmarks,[Puzzles]).

parallel_benchmarks([]) ->
    [];

parallel_benchmarks([{Name,M}|Xs]) ->
    Parent = self(),
    spawn(fun() ->
        Parent !
            {Name,bm(fun()->p_solve(M) end)}
        end),
        Results = parallel_benchmarks(Xs),
    receive
        {Name, Result} -> Results ++ [{Name, Result}]
    end.


parallel_benchmarks() ->
  flush(),
  {ok,Puzzles} = file:consult("problems.txt"),
  timer:tc(?MODULE,parallel_benchmarks,[Puzzles]).


%% check solutions for validity

valid_rows(M) ->
    lists:all(fun valid_row/1,M).

valid_row(Row) ->
    lists:usort(Row) == lists:seq(1,9).

valid_solution(M) ->
    valid_rows(M) andalso valid_rows(transpose(M)) andalso valid_rows(blocks(M)).




    

%visualisation of guess(refine(fill(vegard_hanssen)))
%[[
%   [[1,2,5,8],       [1,8,9],        [1,2,5,8,9],        6,              [2,5,7],        [2,5,7,8],      4,              [1,2,3,5,7,9],  [1,2,7,9]],
%   [7,               [1,8,9],        [1,2,4,5,8,9],      [4,5,8],        [2,4,5],        3,              6,              [1,2,5,9],      [1,2,9]],
%   [[2,4,5,6],       3,              [2,4,5,6],          [4,5,7],        9,              1,              [2,5,7],        8,              [2,7]],
%   [[1,2,3,4,6,8],   [1,6,7,8,9],    [1,2,4,6,7,8,9],    [4,5,7,9],      [2,4,5,7],      [2,4,5,7,9],    [2,7,8,9],      [1,2,7,9],      [1,2,6,7,8,9]],
%   [[2,4,6],         5,              [2,4,6,7,9],        1,              8,              [2,4,7,9],      [2,7,9],        [2,7,9],        3],
%   [[1,2,8],         [1,7,8,9],      [1,2,7,8,9],        3,              [2,7],          6,              [2,7,8,9],      4,              5],
%   [[1,5,8],         4,              [1,5,7,8],          2,              [1,3,5,7],      [5,7,8,9],      [3,5,7,8,9],    6,              [7,8,9]],    
%   [9,               [1,6,7,8],      3,                  [4,5,7,8],      [1,4,5,6,7],    [4,5,7,8],      [2,5,7,8],      [2,5,7],        [2,4,7,8]],
%   [[5,6,8],         2,              [5,6,7,8],          [4,5,7,8,9],    [3,4,5,6,7],    [4,5,7,8,9],    1,              [3,5,7,9],      [4,7,8,9]]
%   ],

%   [ 
%   [[1,2,3,5,8],    [1,3,8,9],      [1,2,5,8,9],        6,              [2,5,7],        [2,5,7,8],      4,              [1,2,3,5,7,9],  [1,2,7,9]],
%   [7,              [1,8,9],        [1,2,4,5,8,9],      [4,5,8],        [2,4,5],        3,              6,              [1,2,5,9],      [1,2,9]],
%   [[2,3,4,5],      6,              [2,4,5],            [4,5,7],        9,              1,              [2,3,5,7],      8,              [2,7]],
%   [[1,2,3,4,6,8], [1,3,7,8,9],     [1,2,4,6,7,8,9],    [4,5,7,9],      [2,4,5,7],      [2,4,5,7,9],    [2,7,8,9],      [1,2,7,9],      [1,2,6,7,8,9]],
%   [[2,4,6],        5,              [2,4,6,7,9],        1,              8,              [2,4,7,9],      [2,7,9],        [2,7,9],        3],
%   [[1,2,8],        [1,7,8,9],      [1,2,7,8,9],        3,              [2,7],          6,              [2,7,8,9],      4,              5],
%   [[1,5,8],        4,              [1,5,7,8],          2,              [1,3,5,7],      [5,7,8,9],      [3,5,7,8,9],    6,              [7,8,9]],
%   [9,              [1,7,8],        3,                  [4,5,7,8],      [1,4,5,6,7],    [4,5,7,8],      [2,5,7,8],      [2,5,7],        [2,4,7,8]],
%   [[5,6,8],        2,              [5,6,7,8],          [4,5,7,8,9],    [3,4,5,6,7],    [4,5,7,8,9],    1,              [3,5,7,9],      [4,7,8,9]]
%  ]]

%[[4,2,3,6,7,8,9,5,1],[5,8,6,1,3,9,7,4,2],[9,1,7,[2,5],4,[2,5],3,6,8],[3,7,[1,4],[2,4],[1,6,8],[1,2,4],5,[2,8],9],[6,[5,9],[1,5],[2,5,7,9],[1,5,8,9],[1,2,3,5,7],[2,8],[2,7,8],4],[2,[4,5,9],8,[4,5,7,9],[5,9],[4,5,7],6,1,3],[[1,7,8],[3,4,5,6],[1,4,5],[4,5,7,9],2,[1,4,5,7],[1,4,8],[7,8],[5,7]],[[1,7],[4,5],9,8,[1,5],[1,4,5,7],[1,2,4],3,6],[[1,7,8],[4,5],[1,2,4,5],3,[1,5],6,[1,2,4,8],9,[5,7]]]
%[[4,2,3,6,7,8,9,5,1],[5,8,6,1,3,9,7,4,2],[9,1,7,[2,5],4,[2,5],3,6,8],[3,7,[1,4],[2,4],[1,6,8],[1,2,4],5,[2,8],9],[6,[5,9],[1,5],[2,5,7,9],[1,5,8,9],[1,2,3,5,7],[2,8],[2,7,8],4],[2,[4,5,9],8,[4,5,7,9],[5,9],[4,5,7],6,1,3],[[1,7,8],[3,4,5,6],[1,4,5],[4,5,7,9],2,[1,4,5,7],[1,4,8],[7,8],[5,7]],[[1,7],[4,5],9,8,[1,5],[1,4,5,7],[1,2,4],3,6],[[1,7,8],[4,5],[1,2,4,5],3,[1,5],6,[1,2,4,8],9,[5,7]]]
