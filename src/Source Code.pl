edge(a,b,5).
edge(b,a,5).
edge(b,c,3).
edge(c,a,2).
edge(c,d,4).
edge(d,b,6).
edge(c,f,4).
edge(f,c,4).
edge(e,c,5).
edge(f,e,7).
edge(g,a,3).
edge(d,g,8).
edge(e,g,2).
edge(f,h,3).
edge(h,i,2).
edge(i,j,3).
edge(j,h,4).
edge(d,h,1).
edge(j,f,6).
edge(l,k,-1).
edge(k,l,4).
edge(a,z,-2).

vertex(a).
vertex(b).
vertex(c).
vertex(d).
vertex(e).
vertex(f).
vertex(g).
vertex(h).
vertex(i).
vertex(j).

costFS(a,20).
costFS(b,10).
costFS(c,5).
costFS(d,8).
costFS(e,12).
costFS(f,18).
costFS(g,9).
costFS(h,7).
costFS(i,14).
costFS(j,2).


%Q1

nonExistent(START, FINISH) :- 
    \+vertex(START),
    format('Vertex ~w of edge (~w,~w) is not a valid vertex.', 
           [START, START, FINISH]), nl;
              
    \+vertex(FINISH),
    format('Vertex ~w of edge (~w,~w) is not a valid vertex.', 
           [FINISH, START, FINISH]), nl.            
           
weightValueCheck(START, FINISH, WEIGHT) :-
    WEIGHT < 1,
    format('Vertex (~w, ~w) has weight ~w which is less than 1.',
           [START, FINISH, WEIGHT]), nl.

weightConsistencyCheck(START, FINISH, WEIGHT) :-
    edge(FINISH, START, REVERSEWEIGHT),
    WEIGHT =\= REVERSEWEIGHT,
    format('Edge (~w, ~w) has weight ~w and edge (~w, ~w) has weight ~w which is inconsistent.',
           [START, FINISH, WEIGHT, FINISH, START, REVERSEWEIGHT]), nl.
    
    
    
    
checkGraph :-
    edge(START, FINISH, WEIGHT),
    (nonExistent(START, FINISH);
    weightValueCheck(START, FINISH, WEIGHT);
    weightConsistencyCheck(START, FINISH, WEIGHT)),
    fail.   %Forces backtracking to ensure all edges are considered.
   
checkGraph.


%Q2
member(X, [H|T]) :-
    memberHelper(T, X, H).

memberHelper(_, X, X).   %If member found, true fact.
memberHelper([H|T], X, _) :-
    memberHelper(T, X, H).
    
    
isSet(L) :-
	is_list(L),
	sort(L, SortedL),   %Removes duplicates.
	sameLength(L, SortedL).

sameLength([], []).     %Both become empty only simultaneoulsy only if same size.
sameLength([_|T1], [_|T2]) :-
	sameLength(T1, T2).
    
    
lastElement(Z, [H|T]) :-
    lastHelper(T, H, Z).

lastHelper([], Z, Z).   %Last element found when the list is now empty.
lastHelper([H|T], _, Z) :-
    lastHelper(T, H, Z).
    
    
append([], L, L).
append([H|T], L, [H|T2]) :-
	append(T, L, T2).
    
 
intersect([], _, []) :- !.
intersect([H|T], B, C) :-
	member(H, B), !,
	C = [H|T2],
	intersect(T, B, T2).
    
intersect([_|T], B, T2) :-
	intersect(T, B, T2).
    
    
%Q3

wPathRoute(X, Y, L, W) :- 
    wPathRouteHelper(X, Y, [], 0, L, W).
    
wPathRouteHelper(X, X, VISITED, ACC_W, L, W) :-
    append(VISITED, [X], L),    %Append the destination to the final returned route.
    W = ACC_W.
wPathRouteHelper(X, Y, VISITED, ACC_W ,L, W) :-
    edge(X, Z, WT),
    \+member(Z, VISITED),
    W1 is ACC_W + WT,
    append(VISITED, [X], P),
    wPathRouteHelper(Z, Y, P, W1, L, W).

 
pathRoute(X, Y, L):- 
    pathRouteHelper(X, Y, [], L).

pathRouteHelper(X, X, VISITED, L) :-   %Target destination found (Base case).
    append(VISITED, [X], L).   
pathRouteHelper(X, Y, VISITED, L):-    %General Case.
    edge(X, Z, _),
    \+member(Z, VISITED),
    append(VISITED, [X], R),
    pathRouteHelper(Z, Y, R, L).
  
  
wPath(X, Y, W):- 
    wPathHelper(X, Y, [], 0, W).

wPathHelper(X, X, _, ACC_W, W) :- 
    W = ACC_W.
wPathHelper(X, Y, VISITED, ACC_W ,W):- 
    edge(X, Z, WEIGHT),
    \+member(Z, VISITED),
    W1 is ACC_W + WEIGHT,   %Accumilate weights.
    wPathHelper(Z, Y, [X|VISITED], W1, W).
        
   
path(X, Y):- 
    pathHelper(X, Y, []).
    
pathHelper(X, X, _).
pathHelper(X ,Y, VISITED):- 
    edge(X, Z, _),
    \+member(Z, VISITED),
    pathHelper(Z, Y, [X|VISITED]).
    
    
wPathAvoidSetRoute(X, Y, SET, L, W) :-
    wPathAvoidSetRouteHelper(X, Y ,SET, [], 0, L, W).
    
wPathAvoidSetRouteHelper(X, X, _, VISITED, ACC_W, L, W) :-
    append(VISITED, [X], L),
    W = ACC_W.
    
wPathAvoidSetRouteHelper(X, Y, SET, VISITED, ACC_W ,L, W) :-
    edge(X, Z, WEIGHT),
    \+member(Z, SET),    %Check the vertex is not within the SET before continuing.
    \+member(Z, VISITED),
    W1 is ACC_W + WEIGHT,
    append(VISITED, [X], P),
    wPathAvoidSetRouteHelper(Z, Y, SET, P, W1, L, W).

    
pathAvoidSetRoute(X, Y, SET, L) :-
    pathAvoidSetRouteHelper(X, Y, SET, [], L).
    
pathAvoidSetRouteHelper(X, X, _, VISITED, L) :-
    append(VISITED, [X], L).
    
pathAvoidSetRouteHelper(X, Y, SET, VISITED, L) :-
    edge(X, Z, _),
    \+member(Z, SET),
    \+member(Z, VISITED),
    append(VISITED,[X], P),
    pathAvoidSetRouteHelper(Z, Y, SET, P, L).   
    
 
%Calculates the longest possible path.
longestPossibleRoute(V) :-
    findall(W,edge(_,_,W), WEIGHTS),    %Retrieve all edge weights as a list.
    sum_list(WEIGHTS, V).
 

shortestPathAvoidSet(X, Y, SET, L, W) :- 
    %Obtain all possible paths to begin with.
    findall([PATH, WEIGHT], wPathAvoidSetRoute(X, Y, SET, PATH, WEIGHT), PATHS),
    PATHS \= [],
    longestPossibleRoute(LONG), 
    LONG1 is LONG + 1,   %Used for initial CUR_W (current shortest path known).
    shortestPathAvoidSetHelper(PATHS, [], LONG1, L, W).
  
shortestPathAvoidSetHelper([], FIN_L, FIN_W, L, W) :-
    L = FIN_L,
    W = FIN_W.
shortestPathAvoidSetHelper([[PATH, WEIGHT]|T], CUR_L, CUR_W, L, W) :-
    (WEIGHT < CUR_W, 
        %If path weight is shortest known, update this by recording path below.
        shortestPathAvoidSetHelper(T, PATH, WEIGHT, L, W), !);
    %Else, keep the current known shortest path, and examine the next path.
    shortestPathAvoidSetHelper(T, CUR_L, CUR_W, L, W).
    
    
%Simply uses `wPathRoute` instead.
shortestPath(X, Y, L, W) :- 
    %Obtain all possible paths to begin with.
    findall([PATH, WEIGHT], wPathRoute(X, Y, PATH, WEIGHT), PATHS),
    PATHS \= [],
    longestPossibleRoute(LONG), 
    LONG1 is LONG + 1,
    shortestPathHelper(PATHS, [], LONG1, L, W).
  
shortestPathHelper([], FIN_L, FIN_W, L, W) :-
    L = FIN_L,
    W = FIN_W.
shortestPathHelper([[PATH,WEIGHT]|T], CUR_L, CUR_W, L, W) :-
    (WEIGHT < CUR_W, 
        shortestPathHelper(T, PATH, WEIGHT, L, W), !);
    shortestPathHelper(T, CUR_L, CUR_W, L, W).

    
%Compute all possible permutations of K vertices.
kSetVert(K, V):- 
    K = 0, !, V = [].
kSetVert(K, V):- 
    K > 0, 
    kSetVertHelper(K, [], V).
    
kSetVertHelper(K, ACC, RES):- 
    K > 0, 
    vertex(X), 
    \+member(X, ACC),
    K1 is K - 1, 
    kSetVertHelper(K1, [X|ACC], RES).
kSetVertHelper(0,ACC, RES):- 
    RES = ACC.

%Test every possible verticy pairing, ensuring there is a path between each.
connectedGraph :-
    forall(kSetVert(2, [START|[FINISH|_] ]),
        path(START, FINISH)).
    
    
%Q4

%returns all the known graph vertices as a list L.
listVertices(L):- listVerticesHelper([], L).
listVerticesHelper(ACC, RES):- 
    vertex(X), 
    \+ member(X, ACC), !,
    listVerticesHelper([X|ACC], RES).
listVerticesHelper(ACC, RES):- 
    RES = ACC.
    
    
buildSST(T, W):-
    listVertices(L), 
    length(L, N),
    (N = 0, !, T = [];  %If there are no vertices only tour is [].
    N > 0, 
    vertex(X),  %Otherwise, choose a starting vertex.
    N1 is N - 1,
    buildSSTHelper(N1, X, X, [X], T, W, 0)).   %Search for possible tours.

%Called when the tour is complete.    
buildSSTHelper(0, START, FINISH, ACC, RES, W, W_ACC):-
    edge(FINISH, START, _),   %Ensure we can return back to the start of the tour.
    append(ACC, [START], NEW_ACC),
    RES = NEW_ACC,
    W = W_ACC.
    
%Called mid tour, 
%`PREV` represents the last vertex added to the tour.
%`START` represents the original starting vertex of the tour.
buildSSTHelper(N, START, PREV, ACC, RES,W, W_ACC) :-
    vertex(X),
    \+member(X, ACC),
    edge(PREV,X,Weight),    %Ensures there is an edge to this next vertex.
    N1 is N - 1,
    NEW_W is W_ACC + Weight,
    append(ACC, [X], NEW_ACC),
    buildSSTHelper(N1, START, X, NEW_ACC, RES, W, NEW_W).
    
    
%BuildSST with the added functionality of inputting a starting vertex.
buildSSTWithStart(V, T, W):-
    listVertices(L), 
    length(L, N),
    (N = 0, !, T = []; 
    N > 0, 
    N1 is N - 1,
    %Required functionality from here on is identical to buildSST.
    buildSSTHelper(N1, V, V, [V], T, W, 0)).  %Call buildSST pre defined helper function.

    
%Q5
%If X is not the least vertex in terms of lexographical ordering.
nonMinLexVertex(X):- 
    vertex(X), 
    vertex(Y), 
    X @> Y.
    
    
%Compute the least vertex X in terms of lexographical ordering.
minLexVertex(X):- 
    vertex(X),
    \+nonMinLexVertex(X).
    
    
vertexInBetween(X, Y, Z):- 
    vertex(X),
    vertex(Y),
    vertex(Z), 
    Y @> Z, 
    Z @> X.

    
%Calculate the immediate successor of X (Y) in the order.
succVertex(X, Y):- 
    vertex(X), 
    vertex(Y), 
    Y @> X, 
    \+ vertexInBetween(X, Y, _).

    
%Calculate all the subsets.
subsetVert(S):- 
    minLexVertex(X), 
    subsetVertHelper([], X, S).
 
subsetVertHelper(ACC, LAST_CONSIDERED, S):- 
    succVertex(LAST_CONSIDERED, X),
    subsetVertHelper(ACC, X, S).
subsetVertHelper(ACC, LAST_CONSIDERED, S):- 
    succVertex(LAST_CONSIDERED, X),
    subsetVertHelper([X|ACC], X, S).
subsetVertHelper(ACC, LAST_CONSIDERED, S):- 
    \+ succVertex(LAST_CONSIDERED, _), S = ACC.

    
%Determine whether vertex V can reach a fire station at any of the vertices given
%(In under or equal to 5 minutes).
reachableFireStation(V, [H|T]) :-
    (wPath(H,V,W), W =< 5, !);  %If one is reachable, no need to check the rest.
    reachableFireStation(V,T).

    
%Take list of nodes, calculate total fire station cost.
totalFireStationCost(L, C) :-
    totalFireStationCostHelper(L, 0, C).
    
totalFireStationCostHelper([H|T], ACC, C) :-
    costFS(H,P),
    NEW_ACC is ACC + P,
    totalFireStationCostHelper(T, NEW_ACC, C).
totalFireStationCostHelper([], ACC, C) :-
    C is ACC.

    
buildSafeSetFSWithinBudget(B,S) :-
    subsetVert(SV),    %Calculate all subsets of vertices.
    forall(vertex(X),
        reachableFireStation(X, SV)), %Ensure every vertex can reach a Fire Station.
    totalFireStationCost(SV, C),
    C =< B,    %Ensure the solution is within budget.
    S = SV.
    
    
%Finds all possible Fire Station placements without a budget concerned.
buildAllSafeSetFS(S) :-
    subsetVert(Ss),
    forall(vertex(X),
        reachableFireStation(X, Ss)),
    S = Ss.

    
%Find the cost of building Fire Stations at every vertex.
highestPossibleCost(TOTAL) :-
    findall(C,costFS(_,C),COSTS),
    sum_list(COSTS, TOTAL).
  
  
computeMinCostSafety(BMIN) :-
    findall(SV,buildAllSafeSetFS(SV),LSV),  %Find all valid station placements.
    LSV \= [],
    highestPossibleCost(T),    %Use highest possible cost + 1 as initial cheapest.
    T1 is T + 1,
    computeMinCostSafetyHelper(LSV, T1, BMIN).
    
computeMinCostSafetyHelper([], CUR_MIN, BMIN) :-
    BMIN = CUR_MIN.
computeMinCostSafetyHelper([H|T], CUR_MIN, BMIN) :-
    totalFireStationCost(H, C),
    (C < CUR_MIN,
        %If placement is cheaper, record this placement.
        computeMinCostSafetyHelper(T, C, BMIN), !);
    %Otherwise, keep current placement recorded and examine next placement.
    computeMinCostSafetyHelper(T, CUR_MIN, BMIN). 
    
    
%Same as computeMinCostSafety, but retains the placement of the cheapest solution.
buildMinCostSafeFS(BMIN,S) :-
    findall(SV,buildAllSafeSetFS(SV),LSV),
    LSV \= [],
    highestPossibleCost(T),
    T1 is T + 1,
    buildMinCostSafeFSHelper(LSV, T1, BMIN, [], S).
    
buildMinCostSafeFSHelper([], CUR_MIN, BMIN, LOCATIONS, S) :-
    BMIN = CUR_MIN,
    S = LOCATIONS.
buildMinCostSafeFSHelper([H|T], CUR_MIN, BMIN, LOCATIONS, S) :-
    totalFireStationCost(H, C),
    (C < CUR_MIN,
        buildMinCostSafeFSHelper(T, C, BMIN, H, S), !);
    buildMinCostSafeFSHelper(T, CUR_MIN, BMIN, LOCATIONS, S).
