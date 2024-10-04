# Formal specification and verification

The purpose of this assignment is to create a formal model of a trash bin system
using the Promela language, formally specify requirements, and verify that your
model satisfies these requirements using Spin.

After this assignment, you will be able to model a software system in the Promela
language and specify requirements as LTL formulas. Further, you will be able to
use the Spin model checker to check whether the model satisfies the given LTL
formulas.

Deadline: Tuesday 22 October 2024
Submission:
    - A single PDF file, uploaded in ANS-Delft, describing the model and the verification. 
    - A ZIP file containing two Promela files, one for the single trash bin system, and one for the multiple trash bins system.

Grading information See Canvas.

You are to complete this exercise in teams of 4 students, as registered on this course’s Canvas page

## Introduction 

In this second assignment, you will model the main controller for a trash bin
system. The context for this assignment is very similar to the trash bin system
from the first assignment.

The assignment requires you to model and verify two different systems: first, a
system that consists of a single trash bin and a single user. Second, a model that
consists of multiple trash bins and users. These two models will be expressed in
the Promela language. The correctness criteria will be specified as formulas in 

linear temporal logic (LTL). The Spin model checker will be used to formally verify
the correctness of the Promela models. We expect that you are familiar with the
Spin model checker by studying the corresponding chapter in the reader and
doing the exercises in that chapter.

## Tasks. 

This assignment is divided into two tasks:

1. The first step is to model a main control process that correctly controls a
single trash bin for a single user. You need to verify, using Spin, that this
control process correctly manages the system. In addition, you will also
model a simple process for a trash truck. See Section 3 for more details.

2. The second step is to generalise the model to account for multiple trash
bins and multiple users. This generalisation mainly requires an adaptation
of the main control process, but the other process types are also mildly
affected. See Section 4 for more details.

Note 1. These tasks may require several iterations. The properties that need to
be verified may lead you to modify your model. Make sure that all properties
are expressed in the corresponding model. In other words, the properties men-
tioned in Section 3 must be expressed in the model of the single trash bin system,
and the properties mentioned in Section 4 must be expressed in the model of the
multiple trash bin system.

Note 2. This assignment contains the requirements for a particular model of the
control software, as opposed to requiring you to use the informal specification
you created when you worked on assignment 1. This is to ensure that your suc-
cess for this assignment does not depend on your result for the previous assign-
ment.

We provide a model of the environment, so that you can focus on modelling the
control software. In Section 2 we describe the model of the environment that we
provide. The assignment for the single trash bin model is described in Section 3,
and the instructions for the multiple trash bin model are in Section 4.

