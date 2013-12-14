\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{ebl}[2013/10/09 v1.0 Brazilian Logic Conference -- Author: Bruno Lopes]

\LoadClass[11pt]{article}

\RequirePackage[T1]{fontenc}
\RequirePackage{ifthen}
\RequirePackage[a4paper,tmargin=3cm,bmargin=2cm,lmargin=3cm,rmargin=3cm]{geometry}
\RequirePackage[portuguese,english]{babel}
\RequirePackage{bookman}
\RequirePackage{booktabs}
\RequirePackage{graphicx}
\RequirePackage{hyperref}
\RequirePackage{natbib}

%Compiler used
\newboolean{pdflatex}
\setboolean{pdflatex}{true}
\newcommand{\uselatex}{\setboolean{pdflatex}{false}}

%Defines authors institutes and acknowledgments
\newboolean{institute}
\setboolean{institute}{false}
\newcounter{inst}
\newcommand{\@institute}{}
\newcommand{\nextinstitute}{\stepcounter{inst}\mbox{}\\\vspace{1em}$\phantom{}^\fnsymbol{inst}$~}
\newcommand{\institute}[1]{\setboolean{institute}{true}\stepcounter{inst}\renewcommand{\@institute}{$\phantom{}^\fnsymbol{inst}$~#1}}
\newcommand{\email}[1]{\mbox{}\\\href{mailto:#1}{\textsf{#1}}}
\newcounter{symb}
\newcommand{\inst}[1]{\setcounter{symb}{#1}$\phantom{}^\fnsymbol{symb}$}
\newboolean{acknowledgement}
\setboolean{acknowledgement}{false}
\newcommand{\acknowledgement}[1]{\setboolean{acknowledgement}{true}\newcommand{\@acknowledgement}{#1}}

\hypersetup{
colorlinks = {true},
linktocpage = {true},
plainpages = {false},
linkcolor = {black},
citecolor = {black},
urlcolor = {black},
unicode = {true},
pdfcreator = {LaTeX2e},
pdffitwindow = {false},
pdfstartview = {FitH},
pdfpagemode = {UseOutlines},
pdfview = {XYZ null null null}
}

\def\@maketitle{
\begin{center}
\setcounter{footnote}{\value{inst}}
\stepcounter{footnote}
{\LARGE {\bf\@title}\ifthenelse{\boolean{acknowledgement}}{\footnote{\@acknowledgement}}{}\par}
\vskip 3em
{\large
\lineskip .75em
\begin{tabular}[t]{c}
\@author
\end{tabular}
\par}
\vskip 1em
\@institute
\end{center}
\par
\vskip 1.5em
}

%References
\bibliographystyle{ebl}
