
\documentclass{article}

% Language setting
% Replace `english' with e.g. `spanish' to change the document language
\usepackage[english]{babel}

% Set page size and margins
% Replace `letterpaper' with `a4paper' for UK/EU standard size
\usepackage[letterpaper,top=2cm,bottom=2cm,left=3cm,right=3cm,marginparwidth=1.75cm]{geometry}

% Useful packages
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{graphicx}
\usepackage[colorlinks=true, allcolors=blue]{hyperref}
\usepackage{mathtools}
\usepackage{thmtools}
\usepackage{enumitem}
\usepackage{xcolor}
\usepackage{amsthm}
\usepackage{csquotes}

% Theorem environments

\theoremstyle{plain}
\newtheorem{assumption}{Assumption}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}

\theoremstyle{definition}
\newtheorem{definition}{Definition}
\newtheorem{example}{Example}

\theoremstyle{remark}
\newtheorem{remark}{Remark}

% Useful commands
\DeclareMathOperator*{\argmax}{arg\,max}
\DeclareMathOperator*{\argmin}{arg\,min}
\DeclareMathOperator{\dom}{dom}
\DeclareMathOperator{\range}{\mathcal{R}}
\newcommand{\E}{\mathbb{E}}
\newcommand{\Prob}{\mathbb{P}}
\newcommand{\is}{{i \in \mathcal{I}}}
\newcommand{\ddo}{{\ddot o}}

\title{Communication \& Trust}
\author{the author}

\begin{document}
\maketitle

\begin{abstract}
Yudkowsky suggested the criterion of \emph{reflective consistency} for decision theories (roughly: does a decision theory choose itself?) \cite{yudkowsky2010timeless}. Dai proposed Updateless Decision Theory (UDT) as a response to Yudkowsky's ideas \cite{dai2009udt}. \cite{demski2025trust} offered the first published proofs of reflective consistency for UDT. However, those results were not entirely satisfying, due to their reliance on strong assumptions. The current work offers a new attempt, inspired by Critch's notion of agent boundaries \cite{Critch2022BoundariesSequence} as well as Garrabrant's work on Cartesian Frames \cite{garrabrant2021cartesian} and Finite Factored Sets \cite{garrabrant2021temporal}. The approach here uses \emph{communication between agent-moments} as a ``release valve'' for pressures which could otherwise lead to self-modification.
\end{abstract}

\section{Introduction}

Self-trust is an important safety property for agentic AI. Without such trust, AI systems have an incentive to modify themselves or create successor agents, which could undermine other safety properties. A better understanding of trust could also contribute to safety in other ways; see \cite{demski2025trust} for further details.

The current paper, like \cite{demski2025trust}, analyzes conditions under which multiple instances of an agent (across space and/or time) can justifiably trust each other. Trust is operationalized as non-interference: given the opportunity to modify how an instance makes decisions, a preference to do so indicates a lack of trust.

Unlike \cite{demski2025trust}, the current paper focuses on \emph{communication} as a means of creating trust. Without communication, coordination problems can create a lack of trust even between agents with shared goals and beliefs. This resulted in overly strong coordination assumptions for previous results. The current work makes coordination assumptions \emph{only with respect to communication itself}, assuming enough for the agent-instances to have a shared communication protocol. This is used to overcome any other coordination problems which could otherwise break trust.\footnote{This strategy owes a significant debt to discussions with Scott Garrabrant, although the strategy he was advocating in those discussions differs considerably from my strategy here.}

Section 2 will provide further historical context for the ideas to be presented here, by contrasting the notion of ``trust'' used here with the common notion of \emph{dynamic consistency}. Section 3 will provide further motivation for the current approach by way of example decision problems.

Section 4 will begin the formal development of these ideas by introducing important notation and mathematical terminology. This includes a notion of factorization inspired by (but distinct from) Garrabrant's work on Finite Factored Sets \cite{garrabrant2021temporal}.
Section 5 will apply these mathematical tools to model agents, inspired by (but distinct from) Garrabrant's Cartesian Frames \cite{garrabrant2021cartesian} and Critch's work on agent boundaries \cite{Critch2022BoundariesSequence}.
Section 6 elaborates this model to deal with multiple instances of an agent and communication between those instances.
Section 7 proves the main result on the avoidance of self-modification.
Section 8 deals with the question of whether agent-instances will follow advice that is communicated to them by other instances.
Section 9 concludes with a discussion of the significance of the results and future work.

Throughout the paper, I will use ``I/my'' to take personal responsibility for decisions/thoughts/etc (EG ``I will call this variable $X$ ...''), and ``we/our'' to invite the reader along (EG ``With this technique, we can ...'').

% DYNAMIC VS REFLECTIVE CONSISTENCY
% current work formalizes trust as non-interference
% this closely resembles dynamic consistency (cite literature)
% dynamic consistency is about whether an agent would agree with its future actions _if it knew them precisely_
% yudkowsy introduced _reflective consistency_ and contrasted it with dynamic consistency (cite tdt paper) but didn't define it precisely
% later work by yudkowsy formalized the _vingean principle_, which distinguishes the type of self-trust yudkowsy wants: agents should trust other instances of themselves _even if they can't precisely anticipate each other's actions_
% this better reflects realistic trust, since realistic agents cannot have everything planned out from the beginning; however, it deprives us of the tool of equilibrium analysis, while asking the same fundamental question of game theory which equilibrium analysis was created to solve (ie, how do we model agents reasoning about each other reasoning about each other reasoning about...)

\section{Trust vs. Dynamic Consistency}

Suppose that an agent has, by virtue of its constitution (biological or synthetic), a specific decision rule. So long as the agent is functioning normally, this decision rule determines how all instances of the agent make decisions. However, the environment might provide some instances of the agent with opportunities to interfere with other instances (or with themselves)\footnote{It may be sensible to assume an instance cannot modify itself, as this would seem to require time-travel. It might further be sensible to assume a temporal partial order, so that later instances can only be influenced by strictly earlier instances. However, the present work avoids such assumptions. This is done to minimize unecessary assumptions, as well as to respect the spirit of Updateless Decision Theory, which is not supposed to rely on any notion of time or causality.}, creating a circumstance where an instance is \emph{not} operating normally, and can make decisions which do not conform to the decision rule. Some agents may prefer to interfere with themselves in such a way. The current work formalizes trust as the absence of such a preference.\footnote{I do not intend to assume that an agent can perfectly identify instances of itself within the environment. What is important is that the agent reasons in such a way as to imagine that there may be instances, and may plan (using its uncertain understanding of the world) to interfere with those instances.}

This closely resembles the concept of \emph{dynamic consistency} which is familiar to both economists and decision theorists \cite{strotz1955myopia, pollak1968consistent, machina1989dynamic, frederick2002time}.\footnote{Dynamic consistency is sometimes alternatively called time consistency or intertemporal consistency.} An agent is dynamically consistent if, \emph{told of its future actions}, it would endorse them.\footnote{More precisely, dynamic consistency is often defined as consistency between the plans an agent would make ahead of time with the decisions which it would make in the moment. However, this amounts to the same thing.} A dynamic inconsistency of this sort implies that an agent would choose to interfere with its future decisions if (a) it had the opportunity to do so, and (b) it could foresee those future decisions precisely.

Yudkowsky contrasts dynamic consistency with \emph{reflective consistency}:\footnote{Pettigrew et al \cite{PettigrewForthcoming-PETOCH} examine a very similar concept which they term \emph{self-recommending} (calling its negation \emph{self-undermining}).}

\begin{displayquote}[\cite{yudkowsky2010timeless}]
I wish to generalize the notion of \emph{dynamic consistency} to the notion of \emph{reflective consistency}. A decision algorithm is \emph{reflectively inconsistent} whenever an agent using that algorithm wishes she possessed a different decision algorithm. Imagine that a decision agent possesses the ability to choose among decision algorithms—perhaps she is a self-modifying Artificial Intelligence with the ability to rewrite her source code, or more mundanely a human pondering different philosophies of decision.
\end{displayquote}

Yudkowsky doesn't offer a precise definition of reflective consistency in that work.\footnote{``I have never seen a formal framework for computing the relative expected utility of different abstract decision algorithms, and until someone invents such, arguments about reflective inconsistency will remain less formal than analyses of dynamic inconsistency.'' \cite{yudkowsky2010timeless}} However, his later work on the concept of \emph{tiling agents} articulates the \emph{Vingean principle}:

\begin{displayquote}[\cite{yudkowsky2013tiling}]
    An agent building a successor (equivalently: a self-modifying agent creating the next generation of its code) should not need to know the successor's exact actions and thoughts in advance.
\end{displayquote}

In the current work, I interpret the Vingean principle as follows: we are not allowed to assume an agent can perfectly predict the strategy of all of its instances. This bars predicting the precise actions of instances (and also bars precise calculation of mixed-strategy equilibria).\footnote{I do not intend this as the only or ultimate interpretation of the Vingean principle. In \cite{yudkowsky2013tiling}, the authors state ``For our purposes we cash out the Vingean principle as follows: \emph{In the parent's reasoning, the offspring's actions should only appear inside quantifiers}.''}

In my experience, those influenced by Yudkowsy's ideas use `tiling' and `reflective consistency' interchangeably. Both terms are, in my opinion, best understood as what the current work calls `self-trust': a variant of dynamic consistency where one does not assume that the agent can foresee the decisions of all its instances. Instead, an agent must reason about itself abstractly, establishing trust in its other instances to do the right thing based on shared goals and properties of the shared decision procedure. This better reflects the problems of self-trust in the real world, since realistic agents cannot precisely plan everything out ahead of time.\footnote{A possible distinction between the current work's notion of `trust' and reflective consistency, on the one hand, and dynamic consistency and tiling on the other hand: the second pair are described in relation to time, whereas the first two deal with `instances' which may be across time or otherwise; however, I see this as a less important distinction.}

Dynamic consistency is sometimes treated as a fundamental rationality constraint; for example, Dutch Book \cite{sep-dutch-book} and Money Pump arguments \cite{gustafsson2022money} can be interpreted as dynamic inconsistency arguments (illustrating a sequence of decisions which an agent would endorse individually, but would not endorse as a plan chosen all at once). I read Yudkowsky as intending to suggest that reflective consistency is equally or more fundamental (and I am inclined to agree). However, Yudkowsky cautions:

\begin{displayquote}[\cite{yudkowsky2013tiling}]
    Therefore I cannot say: If there exists \emph{any} dilemma that would render an agent reflectively inconsistent, that agent is irrational. The criterion is definitely too broad. Perhaps a superintelligence says: "Change your algorithm to alphabetization or I'll wipe out your entire species." [...] To make \emph{reflective inconsistency} an interesting criterion of irrationality, we have to \emph{restrict} the range of dilemmas considered fair. I will say that I consider a dilemma "fair," if when an agent underperforms other agents on the dilemma, I consider this to speak poorly of that agent's rationality.
\end{displayquote}

Yudkowsky goes on to discuss how different notions of fairness will lead one to endorse different decision theories. Yudkowsky endorses a specific notion of fairness, which he calls \emph{decision-determination}.

\begin{displayquote}[\cite{yudkowsky2010timeless}]
    An expected utility maximizer can succeed even on problems designed for the convenience of alphabetizers, if the expected utility maximizer knows enough to calculate that the alphabetically first
decision has maximum expected utility, \emph{and if the problem structure is such that all agents who make the same decision receive the same payoff regardless of which algorithm produced the decision}. This last requirement is the critical one; I will call it \emph{decision-determination}.
\end{displayquote}

The main contributions of the current work are to offer a particular formalization of Yudkowsky's notion of fairness, and prove a result analyzing the reflective consistency (self-trust) of Wei Dai's Updateless Decision Theory.

% reflective consistency vs dynamic consistency
% propose new definition of reflective consistency
% UDT was created for reflective consistency, but no proof
% previous paper offered proofs which were dissatisfying, state reasons
% new formalism and proof
% generalizaiton to multi-agent trust
% can't quite use game-theoretic frame, due to vingean assumption

% MOTIVATING EXAMPLES
% introduce UDT 1.0
% coordination problems: red-room green-room
% UDT 1.1 (is nonvingean)
% coordination problems create trust problems
% communication as a strategy for creating trust
% 5-10-20 version of red/green rooms
% need for an assumption which rules out this counterexample

\section{Motivating Examples}

In response to some of Yudkowsky's ideas about decision theory, Wei Dai proposed Updateless Decision Theory (UDT) \cite{dai2009udt}. Its decision rule is as follows: $$\pi(o) = \argmax_{a \in A} \E(U|\pi(o)=a)$$

Here, $\pi$ is the agent's policy; that is, a function taking observations $o \in O$ and outputting actions $a \in A$. $U$ is the agent's global utility function, and $\E$ takes the expectation in terms of the agent's prior. (This notation will be revised and elaborated later.) This decision procedure achieved self-trust in many examples of interest where other decision procedures failed.

Dai later noticed examples where the above decision rule fails to achieve self-trust \cite{dai2010udt}. These examples are \emph{coordination problems}, where multiple agent-instances must take coordinated action to achieve a desired outcome. For example:

\begin{example}[Coordinated Buttons problem]\footnote{This example is a slight variation on one considered by Wei Dai.}
    You are about to be copied. You will be put in a red room, while your copy will be put in a green room. In both rooms, there are two buttons: one labeled \$5, and another labeled \$10. Each copy can press one button. If you both press matching buttons, then you both receive the amount of money written on that button. Otherwise, you receive no money.
    Before being copied, you have an opportunity to take a pill which will override your thinking for the duration of the problem, giving you the overwhelming reflex to press buttons labeled \$10.
\end{example}

Intuitively, the correct answer is to press the \$10 button, and be indifferent about taking the pill (because you'll do the same thing whether you take the pill or not). Unfortunately, UDT's answer depends on its prior! If you have a sufficiently high prior expectation that you'll press the \$5 button, then both red-room self and green-room self will prefer to press \$5.\footnote{Note that this problem is not ruled out by ditching the Vingean principle. Choosing the \$5 button is a consistent equilibrium; if you expect that's what you'll end up doing, then it is in fact what you end up doing.} If you anticipate this, then you will prefer to take the pill before being copied, reflecting a lack of self-trust.

Dai proposed a revised version of UDT to fix this problem, which he called UDT1.1 (making the original UDT retroactively UDT1, or as I prefer, UDT1.0). The suggested fix was to choose the whole policy at once, rather than choosing actions individually. This solves any potential coordination problems between instances. Unfortunately, it does not suit our purposes here, because it violates the Vingean principle: it requires the agent to plan everything at once, which is not realistic.\footnote{One might quibble over whether \emph{deciding} everything at once violates my version of the Vingean principle, which only forbids requiring the agent to \emph{predict} everything at once; however, it is clear that this should be forbidden for the same reason, namely that it is not cognitively realistic for an agent living in a large world.} (In the rest of this paper, plain UDT refers to UDT1.0, but the reader is cautioned that this convention is not universal.)

The approach taken in this paper instead revolves around \emph{communication}. Notice how UDT does not explicitly model agents with memory. If an agent does have memory, it needs to be modeled as part of the observation. This is a sort of communication between instances.

\begin{example}[Memory problem]\footnote{As far as I know, this example is novel, although it is simple enough that I would not be surprised to find an analogue in the literature.}
    At time one, you will observe a red light or a green light. At time two, you will be offered an option to take one (or none) of two pills; one pill makes you say ``red light" in response to any question for the duration of the problem, while the other does the same for ``green light". After making this choice, you will get your memory wiped, and then (at time three) will be asked to report whether the light at time one was green or red, and rewarded for a correct answer.
\end{example}

Clearly, UDT lacks self-trust in this example; it will take the pill to modify its behavior. However, my contention is that this example is ``unfair'' in some sense: the pill was allowed to accomplish something which the agent's own memory was not allowed to do. In order to narrow things down to cases where self-trust can be treated as a rationality criterion, cases like this need to be ruled out. The intuition behind the present work is that lines of communication should ``exactly parallel'' lines of self-modification: if the agent has the ability to act like it remembers something with a self-modifying pill, then it should also be given the ability to remember normally. (All of this will be formalized later.)

Returning to Coordinated Buttons, the suggestion is this: before being copied, when considering whether to take the pill, you can can think to yourself ``I should press the \$10 button''. Once you are copied, you and the copy can recall this thought and press the \$10 button, secure in the knowledge that there would be no reason for your other instance to change its mind.

This allows communication to act as a release valve for pressures which would otherwise give rise to self-modification. Although it does imply some ability to predict other instances in some cases, it only does this to the extent that self-modification can be predicted; if a self-modifying action has effects which are uncertain in their particulars, then the corresponding self-communication will have similarly uncertain impacts. (This will become clearer when stated formally.) As such, I believe it respects the spirit of the Vingean principle.

Unfortunately, this idea will not be enough to carry us all the way.

\begin{example}[Third Button problem]\footnote{I believe this example is a novel contribution.}
    As in Coordinated Buttons, you are about to be copied, and you have the option of taking a pill which will cause you to press buttons labeled \$10 for the duration of the problem. You also have the option of telling yourself to press \$10 buttons. However, when you get into the red and green rooms, there will be a third button labeled \$20. If both of you press \$5, you both get \$5; if both of you press \$10, you both get \$10; if one of you presses \$10 and the other presses \$20, you both get \$20; in all other cases, you both receive \$0. You have no way to randomize your choices, and you cannot tell yourself to do different things depending on the color of the room (your memory will be wiped in such a case).
\end{example}

This problem seems to be ``fair'' by the standards mentioned so far, yet UDT may still choose self-modification. Depending on its prior, UDT may still need to use the pill to choose \$10. If it instead elects to tell itself to choose \$10, then by the reasoning proposed earlier, each copy would trust that the other copy will follow this instruction; however, if that were true, \emph{this would lead both copies to choose \$20}, resulting in a payoff of \$0.

As such, we will also need to rule out cases like this in order to achieve self-trust. To achieve this, we will need to deal with a conceptual flaw which arises in some interpretations of Yudkowsky's notion of fairness: naively, at least, self-modification is itself a decision, so Yudkowsky's notion of decision-determination fails to rule out universes which ask you to self-modify into an alphabetizer and punish you for not doing so (exactly the scenario Yudkowsky wants to rule out). We can resolve this problem by distinguishing between an agent's \emph{external} observations and actions (these are the observations and actions most typically studied by decision theory), versus \emph{internal} observations and actions (such as recalling or storing memories). A fair environment is, roughly, allowed to depend on external behaviors but not internal behaviors.

The remainder of the paper formalizes these ideas.


\section{Mathematical Preliminaries}

The mathematical formalism used here was significantly inspired by Finite Factored Sets \cite{garrabrant2021temporal}, although it differs considerably in the details, and does not attempt to deal with issues of time or causality.

\subsection{Random Variables}

We work with a probability space $(\Omega, \Prob)$. A \emph{random variable} is a measurable function $X : \Omega \to \range X$ from $\Omega$ to some measurable space $\range X$, which we call the \emph{range} of $X$. We will generally assume our random variables have countable discrete range and finite entropy.

Following standard conventions, we treat random variables as if they are elements of their ranges. For example, if $X$ is a random variable valued in $R$ and $f : R \to S$ is a measurable function, we write $f(X)$ to mean $f \circ X$. Given random variables $X : \Omega \to R$ and $Y : \Omega \to S$, we write $(X, Y)$ for the \emph{product random variable} $\Omega \to R \times S$ defined as $\omega \mapsto (X(\omega), Y(\omega))$.

More generally, if $(X_i)_{i \in I}$ is a family of random variables on $\Omega$, we use the \emph{tuple-builder notation} $(X_i : i \in I, \phi(i))$ to denote the product random variable of those $X_i$ such that $\phi(i)$ holds. The range of this random variable is the product space $\prod_{i : \phi(i)} \range X_i$.

\begin{definition}
If $X$ and $Y$ are random variables on $\Omega$, we say $Y$ \emph{is a function of} $X$ if there exists a measurable function $f : \range X \to \range Y$ such that $Y = f(X)$ almost everywhere. Equivalently, $H(Y | X) = 0$.
\end{definition}

When $Y$ is a function of $X$, we also say $Y$ is a \emph{coarsening} of $X$, or $X$ is a \emph{refinement} of $Y$, or $Y$ is a \emph{subvariable} of $X$. Intuitively, $X$ provides at least as much information as $Y$, since knowing $X$ determines $Y$.

\begin{definition}
If $Y$ is a function of $X$ via $f : \range X \to \range Y$, we call $f$ the \emph{projection} from $X$ to $Y$, and write $`x`_Y = f(x)$ for $x \in \range X$. For a function $g : Z \to \range X$, we define $`g`_Y = f \circ g$.
\end{definition}

\begin{definition}
Given random variables $X$ and $Y$:
\begin{itemize}
    \item The \emph{joint random variable} $(X, Y)$ serves as the coarsest common refinement of $X$ and $Y$: both $X$ and $Y$ are functions of $(X,Y)$.
    \item The \emph{common information} $X \vee Y$ is defined (when it exists) as the finest random variable that is a function of both $X$ and $Y$. Equivalently, it captures exactly the information shared by $X$ and $Y$.
\end{itemize}
\end{definition}

\begin{remark}
Unlike the partition-based framework, where meet and join always exist, the common information $X \vee Y$ may not exist as a single random variable in general. However, it can always be characterized information-theoretically, and in our discrete setting it will exist.
\end{remark}

\subsection{Random Variable Models}

Following the framework of \cite{eisenstat2024condensation}, we package our random variables together with their probability space.

\begin{definition}
A \emph{random variable model} is a countable discrete probability space $\Omega$ with finite entropy, together with a finite family of random variables $(X_i)_{i \in I}$, each with countable discrete range.
\end{definition}

We use subscript notation for joint random variables: if $A \subseteq I$, then $X_A = (X_i : i \in A)$ denotes the product random variable.

\subsection{Factorization}

\begin{definition}
A random variable $X$ \emph{factors as} $(Y, Z)$ if and only if:
\begin{enumerate}
    \item $X = (Y, Z)$ as random variables (i.e., $X$ is the product of $Y$ and $Z$), and
    \item For every $y \in \range Y$ and $z \in \range Z$, there exists $\omega \in \Omega$ with $Y(\omega) = y$ and $Z(\omega) = z$.
\end{enumerate}
\end{definition}

The second condition says that all combinations of values are possible---$Y$ and $Z$ are \emph{independent in support}. This is stronger than merely having $X = (Y, Z)$, which only says that knowing $Y$ and $Z$ determines $X$.

\begin{definition}
When $X$ factors as $(Y, Z)$, there exists a surjective function $m : \range Y \times \range Z \to \range X$, namely $m(y, z) = (y, z)$. We call this the \emph{restriction map}. For fixed $y \in \range Y$, we get a function $m_y : \range Z \to \range X$ given by $m_y(z) = m(y, z)$.
\end{definition}

This notion extends to families of random variables:

\begin{definition}
$X$ \emph{factors as} $(X_i)_{i \in I}$ if and only if there exists a surjective map $m$ from choice functions $c : (i : I) \to \range X_i$ to $\range X$, namely $m(c) = (c(i))_{i \in I}$.
\end{definition}

Here $(a : A) \to B_a$ denotes a dependent function type: the domain is $A$, and for every $a \in A$, $f(a) \in B_a$.

\subsection{Function Decomposition}

\begin{definition}
A function $f : \range X \to \range Y$ \emph{decomposes into} functions $(f_i : \range X_i \to \range Y_i)_{i \in I}$ if:
\begin{enumerate}
    \item $Y$ factors as $(Y_i)_{i \in I}$
    \item Each $X_i$ is a subvariable of $X$
    \item $f(x) = (f_i(`x`_{X_i}))_{i \in I}$ for all $x \in \range X$
\end{enumerate}
\end{definition}

\subsection{Partial Functions}

We write $X \rightharpoonup Y$ for the type of partial functions from $\range X$ to $\range Y$. For $f : X \rightharpoonup Y$, we write $f(x) = \bot$ when $f$ is undefined at $x$. The domain $\dom(f)$ is the set of inputs where $f$ is defined.

\subsection{Probability and Expectation}

We assume a probability measure $\Prob$ on $\Omega$. For a random variable $X$ and value $x \in \range X$, we write $\Prob(X = x)$ for $\Prob(\{\omega : X(\omega) = x\})$.

We will have a utility random variable $U : \Omega \to \mathbb{R}$, assumed bounded with $U(\omega) \in [0, 1]$. The conditional expectation $\E(U | X = x)$ is well-defined when $\Prob(X = x) > 0$. When $\Prob(X = x) = 0$, we stipulate $\E(U | X = x) = -1$.\footnote{This ensures an agent will not choose a probability-zero action. An earlier draft used $\E(U|X=x)=2$ in such cases; however, this causes problems with the ``instances are believed to follow recommendations'' assumption.}


\section{Agents \& Environments}

In this section, we apply the above framework to model agents. This approach takes significant inspiration from Critch's work on agent boundaries \cite{Critch2022BoundariesSequence} and Garrabrant's work on Cartesian Frames \cite{garrabrant2021cartesian}, though it differs considerably in the details.

We model the world using three random variables:

\begin{itemize}
    \item $I$: The \textbf{interior} of the agent, representing persistent state (memories or more complex cognition).
    \item $B$: The \textbf{boundary} of the agent, implementing the decision procedure (handling input/output with the environment).
    \item $E$: The \textbf{external environment}, containing everything in the agent's exterior.
\end{itemize}

For example, if $I$ represents an SSD's state, each value $i \in \range I$ corresponds to a specific bit pattern, and $I(\omega) = i$ means that in world $\omega$, the SSD holds that pattern.

\subsection{Information Flow}

Four random variables mediate information flow between $I$, $B$, and $E$:

\begin{itemize}
    \item $\dot{O}$: The \textbf{internal observation}---memories or internal computations accessible to the decision procedure. $\dot{O}$ is a subvariable of both $I$ and $B$, representing output from $I$ that flows into $B$.

    \item $\ddot{O}$: The \textbf{external observation}---sense data. $\ddot{O}$ is a subvariable of both $E$ and $B$, representing output from $E$ that flows into $B$.

    \item $\dot{A}$: The \textbf{internal action}---data to store/process. $\dot{A}$ is a subvariable of both $I$ and $B$, representing output from $B$ that flows into $I$. Together with $\dot{O}$, this exhausts the overlap between $I$ and $B$: the common information $I \vee B$ equals $(\dot{O}, \dot{A})$.

    \item $\ddot{A}$: The \textbf{external action}---motor commands. $\ddot{A}$ is a subvariable of both $E$ and $B$, representing output from $B$ that flows into $E$. Together with $\ddot{O}$, this exhausts the overlap between $B$ and $E$: the common information $B \vee E$ equals $(\ddot{O}, \ddot{A})$.
\end{itemize}

We define composite random variables:
\begin{itemize}
    \item $O = (\dot{O}, \ddot{O})$: the full observation (all inputs to $B$)
    \item $A = (\dot{A}, \ddot{A})$: the full action (all outputs from $B$)
\end{itemize}

We assume $O$ factors as $(\dot{O}, \ddot{O})$ and $A$ factors as $(\dot{A}, \ddot{A})$.

We also define two subvariables of $\dot{O}$:
\begin{itemize}
    \item $\hat{O}$: the \textbf{semantic observation}---the information the agent is \emph{supposed to} receive when functioning normally.
    \item $\check{O}$: the \textbf{side channel}---aspects of the input that may modify the agent's behavior, causing it to act ``off-policy.''
\end{itemize}

Note that $\hat{O}$ and $\check{O}$ need not factor $\dot{O}$; some semantic observations may be inextricably linked to side-channel effects.

\subsection{Dynamics}

The relationships between these variables are captured by \emph{dynamics}---random variables that encode input-output behavior. Dynamics are examples of what we call \emph{condensation variables}: random variables that represent the ``missing information'' needed to determine an output from an input.

\begin{definition}[Condensation Variable]
Given random variables $X$ and $Y$, a random variable $V$ is a \textbf{condensation variable} for $H(X|Y)$ (the conditional entropy of $X$ given $Y$) if:
\begin{enumerate}
    \item $H(X | Y, V) = 0$ (knowing both $Y$ and $V$ determines $X$)
    \item $V$ is independent of $Y$ in support (all combinations of values are possible)
    \item $H(V) = H(X | Y)$ (V is minimal---it contains exactly the missing information)
\end{enumerate}
\end{definition}

Intuitively, if we think of $Y$ as an input and $X$ as an output, then a condensation variable $V$ captures exactly the additional information needed to compute $X$ from $Y$. The factorization $X = f(Y, V)$ makes the input-output relationship explicit: different values of $V$ correspond to different functions from $Y$ to $X$.

\begin{assumption}[Internal Dynamic]
$I$ factors as $(\dot{A}, D_I)$.
\end{assumption}

The random variable $D_I$ is the condensation variable for $H(I | \dot{A})$---it represents the residual information needed to determine the interior state $I$ given the internal action $\dot{A}$. For a fixed value $d_I \in \range D_I$, there is a function $\iota_{d_I} : \range \dot{A} \to \range I$ giving the interior's response to each internal action. Since $\dot{O}$ is a subvariable of $I$, this yields the input-output function $`\iota_{d_I}`_{\dot{O}} : \range \dot{A} \to \range \dot{O}$.

\begin{assumption}[Environment Dynamic]
$E$ factors as $(\ddot{A}, D_E)$.
\end{assumption}

Similarly, $D_E$ is the condensation variable for $H(E | \ddot{A})$---it represents the residual information needed to determine the environment $E$ given the external action $\ddot{A}$. For $d_E \in \range D_E$, we get $\epsilon_{d_E} : \range \ddot{A} \to \range E$.

\begin{assumption}[Boundary Dynamic]
$B$ factors as $(O, D_B)$.
\end{assumption}

The dynamic $D_B$ is the condensation variable for $H(A | O)$ (equivalently, $H(B | O)$ since $B$ factors as $(O, A)$ up to the action)---it represents the residual information needed to determine the agent's action $A$ given the observation $O$. For $d_B \in \range D_B$, we get $\beta_{d_B} : \range O \to \range B$.

\begin{assumption}[Agent Dynamic Constraint]
$(I, B)$ factors as $(\ddot{O}, D_{I,B})$, where $D_{I,B} = (D_I, D_B)$.
\end{assumption}

This states that the combined agent state $(I, B)$ is fully determined by the external observation and the joint dynamics. We write $\rho_{d_{I,B}} : \range \ddot{O} \to \range(I, B)$ for the resulting function.

\subsection{Notions of Policy}

\begin{definition}
A \textbf{full policy} is a function $\pi : \range O \to \range A$.
\end{definition}

\begin{definition}
The \textbf{effective policy} $\Pi^\dagger$ is the random variable representing the full policy actually implemented by the agent: $\Pi^\dagger = `\beta_{D_B}`_A$, which maps observations to actions.
\end{definition}

We treat $\Pi^\dagger$ both as a set of functions and as a subvariable of $D_B$. This subvariable relationship has a natural interpretation in terms of condensation: the boundary dynamic $D_B$ is the full condensation variable for $H(A|O)$, while the policy $\Pi^\dagger$ is a \emph{coarsening} of $D_B$ that preserves the observation-to-action function while forgetting implementation details. Multiple values of $D_B$ may correspond to the same policy---they represent different ``implementations'' of the same input-output behavior.

\begin{definition}
The \textbf{chosen policy} $\Pi^*$ is the random variable representing the full policy that \emph{would be} implemented if the agent's decision procedure were never modified.
\end{definition}

\begin{definition}
The \textbf{external policy} $\ddot{\Pi}$ is the function $\ddot{\pi} : \range \ddot{O} \to \range \ddot{A}$ that the agent appears to implement from an external perspective: $\ddot{\pi}(\ddot{o}) = `\rho_{d_{I,B}}(\ddot{o})`_{\ddot{A}}$.
\end{definition}

The external policy $\ddot{\Pi}$ is a subvariable of $D_{I,B}$.

\begin{definition}[Abstract Decision Structure]
An \emph{abstract decision structure} consists of random variables $(I, B, E, \dot{O}, \ddot{O}, \dot{A}, \ddot{A}, D_I, D_E, D_B, \hat{O}, \check{O}, \Pi^*, U)$ satisfying all the above definitions and assumptions.
\end{definition}

\begin{definition}[Decision-Determination]
An abstract decision structure is \textbf{decision-determined} if and only if:
\begin{enumerate}
    \item $U$ is a function of $E$, and
    \item $E$ is conditionally independent of $D_{I,B}$ given $\ddot{\Pi}$:
    $$\Prob(E = e \mid D_{I,B} = d_{I,B}) = \Prob(E = e \mid \ddot{\Pi} = `d_{I,B}`_{\ddot{\Pi}})$$
\end{enumerate}
\end{definition}

In words: the external policy is the only thing intrinsic to the agent that impacts the external environment, and utility depends only on the external environment.


\section{Instances \& Communication}

To model agents with multiple instances, we factor the agent by external observation---each value of $\ddot{O}$ defines a different instance.

\subsection{Instance Structure}

\begin{definition}[Instance Factorization]
$B$ factors as $(B_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$. Each $B_{\ddot{o}}$ represents the decision-making for observation $\ddot{o}$. Correspondingly:
\begin{itemize}
    \item $\dot{A}$ factors as $(\dot{A}_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$
    \item $\ddot{A}$ factors as $(\ddot{A}_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$
    \item $A$ factors as $(A_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$, with each $A_{\ddot{o}}$ factoring as $(\dot{A}_{\ddot{o}}, \ddot{A}_{\ddot{o}})$
    \item $\dot{O}$ factors as $(\dot{O}_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$
    \item $\check{O}$ factors as $(\check{O}_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$, each a subvariable of $\dot{O}_{\ddot{o}}$
    \item $\hat{O}$ factors as $(\hat{O}_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$, each a subvariable of $\dot{O}_{\ddot{o}}$
    \item Full policies $\pi$ decompose into \textbf{instance policies} $\pi_{\ddot{o}} : \range \dot{O}_{\ddot{o}} \to \range A_{\ddot{o}}$
    \item $\Pi^*$ factors as $(\Pi^*_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$
    \item $\Pi^\dagger$ factors as $(\Pi^\dagger_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$
\end{itemize}
\end{definition}

\subsection{Communication Structure}

\begin{definition}[Message Semantics]
For each $\ddot{o} \in \range \ddot{O}$, there is a partial function $s_{\ddot{o}} : \range \hat{O}_{\ddot{o}} \rightharpoonup \range \ddot{A}$ giving the semantics: each $\hat{o}_{\ddot{o}}$ either recommends a specific external action or remains silent.

The \textbf{recommendation} $R$ is the random variable whose values are partial functions $r : \range \ddot{O} \rightharpoonup \range \ddot{A}$, where $r(\ddot{o}) = s_{\ddot{o}}(`\dot{O}`_{\hat{O}_{\ddot{o}}})$. $R$ is a subvariable of $\dot{O}$.
\end{definition}

We write $\ddot{\Pi} = R$ to indicate that recommendations are followed: for all $\hat{o}$ and all $\ddot{o} \in \dom(r_{\hat{o}})$, we have $\ddot{\pi}(\ddot{o}) = r_{\hat{o}}(\ddot{o})$.

\begin{definition}[Side-Channel Impact]
For each $\ddot{o}$, there is a partial function $p_{\ddot{o}} : \range \check{O}_{\ddot{o}} \rightharpoonup \range \ddot{A}$ indicating what action is forced by a side-channel value.

The \textbf{forced external policy} $P$ is the random variable with values $q : \range \ddot{O} \rightharpoonup \range \ddot{A}$, where $q(\ddot{o}) = p_{\ddot{o}}(`\dot{O}`_{\check{O}_{\ddot{o}}})$. $P$ is a subvariable of $\dot{O}$.
\end{definition}

\begin{definition}[Modification]
A \textbf{modification} occurs when $\dom(P) \neq \emptyset$. The \textbf{modification probability} of an event $e$ is $m(e) = \Prob(\dom(P) \neq \emptyset \mid e)$.
\end{definition}

\begin{definition}[Concrete Decision Structure]
A \emph{concrete decision structure} is an abstract decision structure satisfying all the instance and communication conditions above.
\end{definition}


\section{Avoiding Self-Modification}

Consider an agent with chosen instance policy determined by UDT:
$$\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = \argmax_{a_{\ddot{o}} \in \range A_{\ddot{o}}} \E[U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}]$$

\begin{definition}
An action $a_{\ddot{o}} \in \range A_{\ddot{o}}$ is \textbf{minimally modifying} at $\dot{o}_{\ddot{o}}$ if:
$$m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \min_{a' \in \range A_{\ddot{o}}} m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a')$$
\end{definition}

\begin{definition}[Communicative Alternative]
For $a_{\ddot{o}} \in \range A_{\ddot{o}}$ and $\dot{o}_{\ddot{o}} \in \range \dot{O}_{\ddot{o}}$, a \textbf{communicative alternative} $ca_{\dot{o}_{\ddot{o}}}(a_{\ddot{o}}) \in \range A_{\ddot{o}}$ satisfies:
\begin{enumerate}
    \item $ca(a_{\ddot{o}})$ is minimally modifying at $\dot{o}_{\ddot{o}}$
    \item For all external policies $\ddot{\pi}$:
    $$\Prob(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \Prob(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}), \ddot{\Pi} = R)$$
\end{enumerate}
\end{definition}

\begin{lemma}[Communicative Expectation]
If a concrete decision structure is (1) decision-determined and (2) has communicative alternatives, then:
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}))$$
\end{lemma}

\begin{proof}
By decision-determination:
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \sum_{\ddot{\pi}} \E(U \mid \ddot{\Pi} = \ddot{\pi}) \Prob(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}})$$

$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}), \ddot{\Pi} = R) = \sum_{\ddot{\pi}} \E(U \mid \ddot{\Pi} = \ddot{\pi}) \Prob(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}), \ddot{\Pi} = R)$$

Since the distributions match by the communicative alternative condition, the expected utilities are equal.
\end{proof}

\begin{theorem}[Self-Trust]
If a concrete decision structure is (1) decision-determined, (2) has communicative alternatives, and (3) has $\Prob(\ddot{\Pi} = R) = 1$, then non-minimally-modifying actions are never strictly preferred by UDT:
$$m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) > \min_{a'} m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a')$$
$$\implies$$
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) \leq \max_{a'} \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a')$$
\end{theorem}

\begin{proof}
Let $a_{\ddot{o}}$ be non-minimally-modifying. By the lemma:
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}), \ddot{\Pi} = R)$$

By condition (3), this equals $\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}))$, which is at most the maximum over all actions.
\end{proof}

Note that condition (3) is about the agent's \emph{subjective} probability---we assume the agent \emph{expects} its instances to follow recommendations.


\section{Following Advice}

\begin{definition}[Stability]
A recommendation $r$ is \textbf{stable} if for all $\ddot{o} \in \dom(r)$, all $\dot{a}_{\ddot{o}}$, and all $\ddot{a}'_{\ddot{o}} \neq r(\ddot{o})$:
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, r(\ddot{o})), [\ddot{\Pi} = r]_{-\ddot{o}}) > \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, \ddot{a}'_{\ddot{o}}), [\ddot{\Pi} = r]_{-\ddot{o}})$$
\end{definition}

\begin{definition}[Internally-Driven Recommendations]
Recommendations are \textbf{internally driven} if for all $\dot{o}, \ddot{o}, \dot{a}, \ddot{a}, \ddot{a}'$:
$$\Prob(R = r \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a})) = \Prob(R = r \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}'))$$
\end{definition}

\begin{theorem}[Advice-Following]
If a concrete decision structure (1) has $\Prob(\ddot{\Pi} = R) = 1$, (2) has internally-driven recommendations, (3) has recommendations that are stable with probability one, and (4) $s_{\ddot{o}}(`\dot{o}`_{\hat{O}}) \neq \bot$, then for all $\ddot{a}_{\ddot{o}} \neq s_{\ddot{o}}(`\dot{o}`_{\hat{O}})$:
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, s_{\ddot{o}}(`\dot{o}`_{\hat{O}}))) > \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, \ddot{a}_{\ddot{o}}))$$

If UDT is the decision rule and instances never receive recommendations and modifications simultaneously, then $\ddot{\Pi} = R$ in fact.
\end{theorem}

\begin{proof}
We show $\argmax_{\ddot{a}} \max_{\dot{a}} \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a})) = r_{`\dot{o}`_{\hat{O}}}(\ddot{o})$.

Decomposing over recommendations to other instances $r_{-\ddot{o}}$:
$$\argmax_{\ddot{a}} \max_{\dot{a}} \sum_{r_{-\ddot{o}}} \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}), r_{-\ddot{o}}) \Prob(r_{-\ddot{o}} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}))$$

Let $\dot{a}$ be optimal given the best $\ddot{a}$. By (1):
$$= \argmax_{\ddot{a}} \sum_{r_{-\ddot{o}}} \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}), [\ddot{\Pi} = r]_{-\ddot{o}}) \Prob(r_{-\ddot{o}} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}))$$

By (2), $\Prob(r_{-\ddot{o}} \mid \cdots)$ is constant in $\ddot{a}$:
$$= \argmax_{\ddot{a}} \sum_{r_{-\ddot{o}}} \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}), [\ddot{\Pi} = r]_{-\ddot{o}})$$

By (3) and (4), this equals $r_{`\dot{o}`_{\hat{O}}}(\ddot{o})$.
\end{proof}


\section{Conclusion}

Yudkowsky's notion of fairness (decision-determination) arguably had a conceptual flaw: self-modification is itself a decision, so decision-determination does not rule out problems that directly incentivize self-modification.

I interpreted decision-determination to avoid this problem by distinguishing internal from external actions. A ``fair problem'' is one where the universe doesn't care about internal makeup except through external choices.

However, decision-determination still isn't enough. Section 3 provided counterexamples where self-trust fails without it being the decision procedure's fault.

Theorem 1 showed self-trust for UDT under three conditions: decision-determination, communicative alternatives, and belief that one follows advice. Theorem 2 showed that advice-following belief is self-fulfilling under further conditions of internally-driven recommendations, stable recommendations, and mutual exclusivity of recommendations and modifications.

I suggest fairness consists of at least decision-determination, communicative alternatives, and stable recommendations. Something like $\Prob(\ddot{\Pi} = R) = 1$ also seems necessary---a form of ``self-esteem.''

Future work could:
\begin{itemize}
    \item Transform these ideas into a representation theorem
    \item Model computational uncertainty properly
    \item Generalize to agents without shared goals/beliefs
    \item Generalize to agents without shared ontology
\end{itemize}



\bibliographystyle{alpha}
\bibliography{sample}

\end{document}
