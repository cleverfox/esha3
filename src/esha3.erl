-module(esha3).
-export([shake_128/2, shake_256/2]).
-export([sha3_224/1, sha3_256/1, sha3_384/1, sha3_512/1]).
-export([keccak_224/1, keccak_256/1, keccak_384/1, keccak_512/1]).

-record(calc, {
          inbin = {0,0,0,0,0},
          t = 0,
          state = undefined
         }).

shake_128(Data, Len) -> shake(128, Len, Data).
shake_256(Data, Len) -> shake(256, Len, Data).

sha3_224(Data) -> sha3(224, Data).
sha3_256(Data) -> sha3(256, Data).
sha3_384(Data) -> sha3(384, Data).
sha3_512(Data) -> sha3(512, Data).

keccak_224(Data) -> keccak(224, Data).
keccak_256(Data) -> keccak(256, Data).
keccak_384(Data) -> keccak(384, Data).
keccak_512(Data) -> keccak(512, Data).

keccak(Bits, Data) ->
  hash(Bits div 8, Data, 200 - (Bits div 4), 1).

sha3(Bits, Data) ->
  hash(Bits div 8, Data, 200 - (Bits div 4), 16#06).

shake(Bits, Len, Data) ->
  hash(Len, Data, 200-(Bits div 4), 16#1F).

rol(X, S) ->
    X1 = X bsl S,
    Y1 = X1 bsr 64,
    (X1 band 16#FFFFFFFFFFFFFFFF) + Y1.

binary_new(Size) ->
  <<0:(Size*8)/big>>.

xorin(Dst, Src, Offset, Len) ->
  New = crypto:exor(
          binary_part(Src, Offset, Len),
          binary_part(Dst, 0, Len)
         ),
  Dst2 = binary_put(Dst, 0, New),
  {Dst2, Src}.

binary_put(Bin, Offset, New) ->
  eevm_ram:write(Bin, Offset, New).

% P*F over the full blocks of an input.
foldP(A, Inbin, Len, Fun, Rate) when Len >= Rate ->
  {A1, Inbin1} = Fun(A, Inbin, byte_size(Inbin) - Len, Rate),
  A2 = keccakf(A1),
  foldP(A2, Inbin1, Len - Rate, Fun, Rate);

foldP(A, Inbin, Len, _Fun, _Rate) ->
  {A, Inbin, Len}.

binary_xor(Var, Index0, Value) ->
    Index = trunc(Index0),
    C = crypto:exor(binary_part(Var, Index, 1), Value),
    binary_put(Var, Index, C).

setout(Src, Dst, Offset, Len) ->
    New = binary_part(Src, 0, Len),
    Dst2 = binary_put(Dst, Offset, New),
    {Src, Dst2}.

hash(Outlen0, Source, Rate, Delim) ->
  Outlen = trunc(Outlen0),
  Inlen = trunc(byte_size(Source)),
  Rate = trunc(Rate),

  % // Absorb input.
  A0 = binary_new(200),
  {A1, _, Inlen1} = foldP(A0, Source, Inlen, fun xorin/4, Rate),
  % // Xor source the DS and pad frame.
  A2 = binary_xor(A1, Inlen1, <<Delim>>),
  A3 = binary_xor(A2, Rate - 1, <<16#80>>),
  % // Xor source the last block.
  {A4, _Source} = xorin(A3, Source, trunc(byte_size(Source) - Inlen1), Inlen1),
  % // Apply P
  A5 = keccakf(A4),
  % // Squeeze output.
  Out = binary_new(Outlen),
  {A6, Out, Outlen} = foldP(A5, Out, Outlen, fun setout/4, Rate),
  {_a, Out2} = setout(A6, Out, 0, Outlen),
  Out2.

binary_a64(<<>>, Tuple) ->
  Tuple;
binary_a64(<<Bin:64/little-unsigned, Rest/binary>>, Tuple) ->
  binary_a64(Rest, erlang:append_element(Tuple, Bin)).

for_n(N, Step, Acc, Fun) ->
  lists:foldl(
    fun(I, Acc1) ->
        Fun(I * Step, Acc1)
    end,
    Acc,
    lists:seq(0, N - 1)
   ).

f1(Acc0) ->
  for_n(5, 1, Acc0,
        fun(X, IAcc0 = #calc{inbin=Inbin0}) ->
            Inbin1 = setelement(1+X, Inbin0, 0),

            for_n(5, 5, IAcc0#calc{inbin=Inbin1},
                  fun(Y, Acc = #calc{state=State, inbin=Inbin}) ->
                      Ret = element(1+X, Inbin) bxor element(1+X+Y, State),
                      Inbin2 = setelement(1+X, Inbin, Ret),
                      Acc#calc{inbin=Inbin2}
                  end)
        end).

f2(Acc1) ->
  for_n(5, 1, Acc1, 
        fun(X, Acc) ->
            for_n(5, 5, Acc, 
                  fun(Y, IAcc = #calc{state=State, inbin=Inbin}) ->
                      Ret =
                      (element(1+((X + 4) rem 5),Inbin)
                       bxor 
                       rol(element(1+((X + 1) rem 5), Inbin), 1)
                      )
                      bxor
                      (element(1+ Y + X, State)),

                      OState=setelement(1+X+Y, State, Ret),
                      IAcc#calc{state=OState}
                  end)
        end).

f3(Acc3) ->
  for_n(24, 1, Acc3, 
        fun(X, #calc{state=State,
                     inbin=Inbin,
                     t=T}) ->
            Inbin2 = setelement(1+0, Inbin, element(1+pi(X), State)),
            State2 = setelement(1+pi(X), State, rol(T, rho(X))),
            #calc{t= element(1+0, Inbin2),
                  state=State2,
                  inbin=Inbin2}
        end).

f4(Acc4) ->
  for_n(5, 5, Acc4, 
        fun(Y, Acc) ->
            Acc1 =
            for_n(5, 1, Acc, 
                  fun(X, IAcc = #calc{state=State, inbin=Inbin}) ->
                      Inbin1 = setelement(1+X, Inbin, element(1+Y+X, State)),
                      IAcc#calc{inbin=Inbin1}
                  end),

            for_n(5, 1, Acc1,
                  fun(X, IAcc = #calc{state=State, inbin=Inbin}) ->
                      Ret =
                      bnot(element(1+((X + 1) rem 5), Inbin))
                      band(element(1+((X + 2) rem 5), Inbin))
                      bxor(element(1+X, Inbin)),

                      State2 = setelement(1+Y+X, State, Ret),
                      IAcc#calc{ state=State2}
                  end)
        end).

theta(I, Acc0) ->
  % // Theta
  Acc1 = f1(Acc0),

  _Acc2=#calc{state=State2, inbin=Inbin2} = f2(Acc1),

  % // Rho and pi
  Acc3 = #calc{t=element(1+1,State2),
              state=State2,
              inbin=Inbin2},
  Acc4 = f3(Acc3),
  % // Chi
  Acc5 = #calc{state=State} = f4(Acc4),

  % // Iota
  Acc5#calc{state=setelement(1+0, State, element(1+0, State) bxor rc(I))}.

-define(RC,
        {1, 16#8082, 
         16#800000000000808A,
         16#8000000080008000, 16#808B, 16#80000001, 16#8000000080008081,
         16#8000000000008009, 16#8A, 16#88, 16#80008009, 16#8000000A, 16#8000808B, 16#800000000000008B,
         16#8000000000008089, 16#8000000000008003, 16#8000000000008002, 16#8000000000000080, 16#800A,
         16#800000008000000A, 16#8000000080008081, 16#8000000000008080, 16#80000001, 16#8000000080008008}
       ).

rc(Index) ->
  element(1+Index, ?RC).

-define(PI, {10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1}).

pi(Index) ->
  element(1+Index, ?PI).

-define(RHO, {1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44}).

rho(Index) ->
  element(1+Index, ?RHO).


keccakf(A) ->
  Acc0 = #calc{state=binary_a64(A, {})},

  FR=for_n(24, 1, Acc0, fun theta/2),
  Ret=a64_binary(FR#calc.state),
  Ret.

a64_binary(Tuple) ->
  iolist_to_binary(
    [ <<E:64/little-unsigned>> || E <- tuple_to_list(Tuple) ]
   ).


