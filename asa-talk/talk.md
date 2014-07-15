Well-typed smart fuzzing

# The story

+ Thomas's interview at Cryptosense. Nice problem, came home, found
  two other implementation of the key data-structure.
+ How do I check that these two implementation do the same thing?
+ Let's run the two implementation together on test cases, and see
  that they related results.
+ Wait, can I generate test cases from the data structure's API?
  + Quickcheck: automatic generation of test cases based on the
  internal representation of types, at the function level
  + Articheck: automatic generation of test cases based on the API, at
  the API level
+ How to test an API
  + Generate random arguments and call the function -> Fuzzing
  + Unlikely to succeed (one cannot squeeze an apple)
  + Use the types to reduce the fuzzing space! (Well-typed does not
    mean well-formed, though)
+ What is specific to data-structures?
  Nothing.
+ The pitch: We have a principled way to exercise an API in a type
  safe manner, both for safety and security purposes.
+ The end of the story: Wrote a paper about that with two friends,
  then left academia to work at Cryptosense. In this talk, we will see
  how our naive academic was refined by working in an industrial
  context.

# API-ML

+ How to describe APIs?

+ In this talk, APIs are a set of functions in a first-order language.
```
type template
type key
type text
val generate_key: template -> key
val wrap: key -> key -> text
val encrypt: key -> text -> text
```

+
```
type 'a ty =
{name: string;
 mutable content: 'a list}

type 'a fd =
| return : 'a ty -> 'a fd
| @~> : 'a ty * 'b fd -> ('a -> 'b) fd

type 'a fn = Fun : (string * 'a fd * 'a) -> 'a fn
```

```
let int_ty =
{name = "int";
 content = [1;2;3;42]
}

let add = Command ("add", (int_ty @~> int_ty @~> int_ty), (+))
```

+ The monkey: pick one int, pick one int, apply the function, if the
  result is new, add it to the set of possible choices. Loop.

+ By repeatingly applying the functions of our APIs (here, add), we can
  build *new instances* of the type int.

+ The description of the types of the functions guide the exploration.

+ Works for stateless APIs.

# The DSL
+ The DSL of types
  + We have abstract types (types that the user/attacker cannot open)
  + We have products and sums
  + We have subset types (for instance, a function that takes as
    arguments the set of public keys rather than the whole set of
    keys)
  + We have bijections
  + We could have maps
  + This is Dolev-Yao style: the attacker can open products and sums
    (e.g., change the PIN block format a PIN block pretend to have).
+ The DSL of APIs First order functions. Use cases: data structures,
  bindings to a DSl, binary protocols over the network. (Use cases in
  each of these).

# Taming the combinatorial explosion
+ The structure of the types define a combinatorial search space with
  two types of strategies: Constants (that are known in advance) and
  variables (that are discovered). Eg. template * template vs key *
  template.
+ A library of efficient, low memory footprint finite enumerators
+ The comparison functions are quotients. (BDDs vs BDTs)
+ We enumerate a combinatorial problem that is a moving target:
  adding new inhabitants to types changes the state space.
+ The secret sauce: a mechanism that makes it possible to compute a
  good approximation of the next elements to consider, with a low
  memory/computationnal cost.
+ PKCS#11, 1M tests per hour (measure the runtime of the operation)

# Use cases
+ Data structures APIs
+ The Cryptosense pipeline: Testing -> Learning -> Model checking
+ API fuzzing as a service: RESTful

