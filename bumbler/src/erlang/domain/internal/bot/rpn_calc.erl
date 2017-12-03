%% @see http://learnyousomeerlang.com/static/erlang/calc.erl
-module(rpn_calc).
-export([rpn_calc/1, rpn_calc_test/0]).

%% rpn_calc(List()) -> Int() | Float()
%% parses an RPN string and outputs the results.
rpn_calc(InputString) when is_list(InputString) ->
    [Res] = lists:foldl(fun rpn/2, [], string:tokens(InputString, " ")),
    Res.

%% rpn(Str(), List()) -> List()
%% Returns the new stack after an operation has been done.
%% If no operator is found, we assume a number.
rpn("+", [N1,N2|S]) -> [N2+N1|S];
rpn("-", [N1,N2|S]) -> [N2-N1|S];
rpn("*", [N1,N2|S]) -> [N2*N1|S];
rpn("/", [N1,N2|S]) -> [N2/N1|S];
rpn("^", [N1,N2|S]) -> [math:pow(N2,N1)|S];
rpn("ln", [N|S])    -> [math:log(N)|S];
rpn("log10", [N|S]) -> [math:log10(N)|S];
rpn("sum", Stack)   -> [lists:sum(Stack)];
rpn("prod", Stack)  -> [lists:foldl(fun erlang:'*'/2, 1, Stack)];
rpn(X, Stack) -> [read_num(X)|Stack]. % no operator is found, assume number

%% read_num(String()) -> Int() | Float()
read_num(N) ->
    case string:to_float(N) of
        {error,no_float} -> list_to_integer(N); % error, not a number;
        {F,_} -> F                              % else is a number
    end.

%% returns 'ok' iff successful
rpn_calc_test() ->
    5 = rpn_calc("2 3 +"),
    87 = rpn_calc("90 3 -"),
    -4 = rpn_calc("10 4 3 + 2 * -"),
    -2.0 = rpn_calc("10 4 3 + 2 * - 2 /"),
    ok = try
        rpn_calc("90 34 12 33 55 66 + * - +")
    catch
        error:{badmatch,[_|_]} -> ok
    end,
    4037 = rpn_calc("90 34 12 33 55 66 + * - + -"),
    8.0 =  rpn_calc("2 3 ^"),
    true = math:sqrt(2) == rpn_calc("2 0.5 ^"),
    true = math:log(2.7) == rpn_calc("2.7 ln"),
    true = math:log10(2.7) == rpn_calc("2.7 log10"),
    50 = rpn_calc("10 10 10 20 sum"),
    10.0 = rpn_calc("10 10 10 20 sum 5 /"),
    1000.0 = rpn_calc("10 10 20 0.5 prod"),
    ok.

