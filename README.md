Pico-C
=========


What is this
------------

This project is the implementation of a set of changes to the language specifications of Pico and is part of the exam for the course "Interpretatie van Computerprogramma's II".


Context
-------

This is the Pico interpreter written in C. 
Pico is an experimental language, inspired by Scheme but presenting a conventional syntax (without losing Scheme features such as for instance variable size argument lists) and using tables instead of pairs as composite data constructs. More importantly, Pico has extremely simple semantics (more so than Scheme) which allows us to build the virtual machine directly on top of the abstract grammar in a very straightforward and powerful continuation based style.

Pico is used as a didactic tool in the course "Interpretatie van Computerprogramma's II" which is part of the computer science curriculum organized by the computer science department of the faculty of sciences of the Vrije Universiteit Brussel. It is a course (first issue in its current form in the academic year 1996/1997) organized under the responsibility of Theo D'Hondt.

The ambition is to conceive and construct a virtual machine for Pico from the ground up. The target is an ordinary computing platform (e.g. a personal computer) equipped with an ANSI C programming environment; the virtual machine is an 8000 line C program that implements the various essential components such as memory manager, stack machine, parser, native functions &c. The aim of this course is to put to practice what was acquired in the first year, to introduce students to the full design process and to expose them to a large scale software engineering project that has concrete relevance.

All software artifacts used in this course are built either in Pico or in C. The Pico virtual machine itself is built in ANSI C; since it is a fully operational Pico interpreter, the only software that is required is a C programming environment.


Project assignment
------------------

Add Lazy Tables to Pico.   
(Dutch) [Assignment](https://github.com/ivakhnov/Pico-C/blob/master/LazyTables_opgave.pdf)    
Following code examples should make it clear:    



	f(x): t[::]: x+i
	<function f>
		
	> lazy_table: f(42)
	[: ... :]

	> lazy_table[:2:]
	44

	> lazy_table
	[: <lazy>, 44, ... :]


and


	> t[::]: { display("Hello "); "World!" }
	[: ... :]

	> t[:2:]
	Hello World!

	> t[:2:]
	World!
	  
	>t
	[: <lazy>, World!, ... :]


also


	> integers[::]: i
	[: ... :]

	> integers[:2:]
	2

	> integers
	[: <lazy>, 2, ... :]

	> sum_till(t): sum[:t[:1:]:]: t[:i:] + sum[:i-1:]
	<function sum_till>

	> s: sum_till(integers)
	[: 1, ... :]

	> s[: 3 :]
	6

	>s
	[: 1, 3, 6, ... :]


This means that this schould give any asked fibonacci number:

	> fibs[: 1, 1 :]: fibs[:i-1:]+fibs[:i-2:]
	[: 1, 1, ... :]



Links
-----

- [Pico on Wikipedia](https://en.wikipedia.org/wiki/Pico_%28programming_language%29)
- [Official Pico page](http://pico.vub.ac.be/)
- [Software Languages Lab](http://soft.vub.ac.be/soft/)
