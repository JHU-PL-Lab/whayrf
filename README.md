Whayrf
======

Proof of concept of the paper "What is Your Function? Static Pattern Matching on
Function Behavior".

Caveats
-------

Whayrf is a monomorphic system, which means programs that use the same syntactic
function more than once may not behave as expect. A source code transformation
is possible to support polymorphism, refer to section 3.3 of the paper for
further discussion.

Usage
-----

There are two different ways to setup and run Whayrf.

### OPAM

1. Make sure you have [OCaml][ocaml] and [OPAM][opam] installed on the latest
   version:

    $ opam update
    $ opam upgrade
    $ opam switch 4.02.1

2. Install the dependencies:

    $ opam install oasis batteries menhir ounit

3. Generate configuration:

    $ oasis setup -setup-update dynamic

4. Configure:

    $ ./configure

5. Enable tests:

    $ ocaml setup.ml -configure --enable-tests

6. Build:

    $ make

7. Interact with the toploop (sample programs can be found at `test-sources/`):

    $ ocamlrun whayrf_toploop.byte

8. Run the tests:

    $ make test

### Docker

Having [Docker][docker] and [Docker Compose][docker-compose] installed, run:

    $ docker-compose run --rm whayrf

This builds and runs the tests.

In order to interact with the toploop (sample programs can be found at
`test-sources/`):

    $ docker-compose run --rm whayrf 'ocamlrun whayrf_toploop.byte'

Authors
-------

- Leandro Facchinetti <lfacchi2@jhu.edu>.
- Pottayil Harisanker Menon <pharisa2@jhu.edu>.
- Zachary Palmer <zachary.palmer@jhu.edu>.
- Alexander Rozenshteyn <arozens1@jhu.edu>.
- Scott F. Smith <scott@jhu.edu>.

The Johns Hopkins University


[ocaml]: https://ocaml.org/
[opam]: https://opam.ocaml.org/
[docker]: https://www.docker.com/
[docker-compose]: https://docs.docker.com/compose/
