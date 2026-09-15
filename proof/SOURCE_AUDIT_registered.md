# Source audit and claim boundary — R44

## Supplied inputs actually used

The supplied preceding archive `einstein_reverse_descent.zip` was extracted and its complete replay executed successfully in this turn (including its recursive-interface dependency). It is retained unchanged under `upstream/`. Its SHA256 is `ac6016d8e72b36abcf41a0250dfd456633714825315c41cb3623a0879a642243`.

The earlier carrier P, the 192-position small-pyramid construction, exact signed-contact methods, and the previous 62-to-398 reverse-admissibility failure come from that source chain. Their use is not represented as new discovery.

The current frame table, 44-contact atlas, forced-parent proof, self-preserving parent language, solid R44, unrestricted feature-alignment lemmas, all-mate collision census, and resulting unrestricted aperiodicity submission are new work in this batch. The chosen child rotations are not the old fixed-frame hierarchy, so its arbitrary-compact replacement no-go theorem does not apply unchanged.

The underlying SBT source was read directly from the provided corpus archive, not inferred from a catalog description. Entry: `Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex`; source SHA256 `4754d40ef9d943eb507c963124827ae8678cbd1cc05c83404d235547d4c27722`. The following excerpts retain its terminology.

## Interpretation and verification limits

F7 is not used to call an invertible map lossy. The old problem was admissibility after coarsening; here that gate is tested by exact equality of contact sets. F12 is a diagnostic for missing distinctions, not a geometric compiler. F28 motivates separating nonempty existence, recognizability, and admissibility preservation. Their actual tiling instances are proved by the new geometry and finite computations.

The full proposed Einstein theorem has not received external adversarial review. The unrestricted edge/solid-angle argument is a written proof, not a Lean theorem. The finite counters and exact mesh were independently replayed without a solver. No novelty priority or acceptance by the mathematical community is claimed.

## External context, not an imported construction

Goodman-Strauss, *Matching rules and substitution tilings*, Annals of Mathematics 147 (1998), 181–223, DOI 10.2307/120988, was consulted for the distinction between an unmarked substitution carrier and a decorated system enforcing a hierarchy. Smith, Myers, Kaplan and Goodman-Strauss, *An aperiodic monotile*, arXiv:2303.10798, was consulted for context. Neither supplies the new one-solid construction or the unrestricted-alignment proof; no theorem from them is needed to verify the R44 argument.

The current work is not a comprehensive novelty search.

## F7: sufficiency

```text
1837: \subsection{Sufficiency Closure}\label{sec:stability:sufficiency-closure}
1838: 
1839: Fix a closure package with history carrier \(H\), current quotient
1840: map \(q:H\to\currQ\), and a declared family \(\mathcal F\) of future
1841: probes.  The family is the apparatus's announcement of which future
1842: observables will be tested at this interface; it is not a claim of
1843: sufficiency for every possible future question.
1844: 
1845: \begin{theorem}[Sufficiency Closure]\label{thm:F7}
1846: The current quotient \(\currQ\) is sufficient for the declared future
1847: family \(\mathcal F\) if and only if every declared future probe
1848: \(f\in\mathcal F\) descends through \(q\).  Equivalently, for every
1849: \(f:H\to F_f\) in \(\mathcal F\) there is a map
1850: \(\overline f:\currQ\to F_f\) such that
1851: \[
1852:   f=\overline f\circ q .
1853: \]
1854: \end{theorem}
1855: \footnote{Verified in Lean as
1856: \texttt{Stability.SufficiencyClosure.\allowbreak{}sufficiency\_closure};
1857: see \Cref{app:formalization}.}
1858: \begin{proof}
1859: Assume first that every declared future probe descends through
1860: \(q\).  Then each future value \(f(h)\) is determined by the current
1861: class \(q(h)\).  Hence two histories with the same current quotient
1862: have the same value under every declared future probe, so no
1863: declared future distinction remains hidden inside a current fiber.
1864: This is precisely sufficiency for the declared family.
1865: 
1866: Conversely, suppose \(\currQ\) is sufficient for the declared future
1867: family.  For a probe \(f:H\to F_f\), define a candidate lower map on
1868: a current class \(q(h)\) by \(\overline f(q(h))=f(h)\).  Sufficiency
1869: is exactly the assertion that this assignment is independent of the
1870: chosen representative: if \(q(h)=q(h')\), then the declared future
1871: record gives \(f(h)=f(h')\).  Therefore \(\overline f\) is
1872: well-defined and satisfies \(f=\overline f\circ q\).  Since \(f\)
1873: was arbitrary, every declared future probe descends through the
1874: current quotient.
1875: \end{proof}
1876: 
1877: The interaction status is \(\BirdInt\)-compatible because the future
1878: probes are declared interactions and the sufficiency claim is audited
1879: relative to that declaration.  The theorem does not enumerate the
1880: declared future probes; that choice belongs to the apparatus.  It
1881: also does not assert sufficiency for undeclared probes, which lie
1882: outside the current audit scope.
1883: 
```

## F12: no free distinction

```text
940: \subsection{No-Free-Distinction}\label{sec:access:no-free-distinction}
941: 
942: Keep the formed access quotient \(\accessQ:H\to Q_I\) from
943: Quotientality, together with the no-overread discipline from
944: Adequacy.  A proposed new current distinction is a readout
945: \(d:H\to D\).  Its split-pair obstruction at fixed access is
946: \[
947:   \splitObs_{\mathrm{dist}}(\accessQ,d)
948:   =
949:   \{(h,h')\mid \accessQ(h)=\accessQ(h')\ \text{and}\ d(h)\ne d(h')\}.
950: \]
951: 
952: \begin{theorem}[No-Free-Distinction]\label{thm:F12}
953: A functorial gate using only the existing access quotient cannot
954: produce a strict new current distinction.  If a readout
955: \(d:H\to D\) is current-visible without additional apparatus data,
956: then
957: \[
958:   \splitObs_{\mathrm{dist}}(\accessQ,d)=\varnothing,
959:   \qquad\text{equivalently}\qquad
960:   d=\overline d\circ\accessQ
961: \]
962: for some \(\overline d:Q_I\to D\).  If the obstruction is nonempty,
963: the distinction requires declared memory data, bridge data, residual
964: budget, scope change, or an enlarged calibration family.
965: \end{theorem}
966: \footnote{Verified in Lean as
967: \texttt{Access.NoFreeDistinction.no\_free\_distinction}.}
968: \begin{proof}
969: A gate that uses only the existing quotient can depend only on the
970: class \(\accessQ(h)\).  Therefore any readout it produces is
971: constant on the fibers of \(\accessQ\), and the displayed
972: split-pair obstruction is empty.  By \Cref{thm:F10}, this is
973: equivalent to the existence of a factorization
974: \(d=\overline d\circ\accessQ\).
975: 
976: Conversely, if \(\splitObs_{\mathrm{dist}}(\accessQ,d)\) is
977: nonempty, then \(d\) separates two histories that the current access
978: quotient identifies.  Treating \(d\) as a current exact distinction
979: would therefore overread the available access, contradicting
980: \Cref{thm:F11}.  The only lawful way to use \(d\) is to add declared
981: apparatus data: a memory record, a bridge, a budgeted residual, a
982: scope restriction, or a stronger calibration family.
983: \end{proof}
984: 
985: The theorem is not anti-refinement.  Calibration families may enrich
986: the apparatus, and strict extensions may add real distinctions.  The
987: claim is only that the enrichment must be declared and statused, not
988: smuggled in as a free consequence of the old access quotient.  Nor
989: does this theorem classify every possible source of new data; later
990: axes treat memory, bridges, residual budgets, scope changes, and
991: predictive refinements in their own normal forms.
```

## F28: composability

```text
5389: \subsection{Composability}\label{sec:status-records-coherence:composability}
5390: 
5391: \begin{theorem}[Composability]\label{thm:F28}
5392: Let \(X_A,X_B\) be component spaces with quotients
5393: \(q_A:X_A\to Q_A\), \(q_B:X_B\to Q_B\), interface readouts
5394: \(\beta_A:X_A\to I_A\), \(\beta_B:X_B\to I_B\), composition
5395: \(U:X_A\times X_B\to X_{AB}\), composite quotient
5396: \(q_{AB}:X_{AB}\to Q_{AB}\), admissibility predicate
5397: \(\operatorname{Adm}:X_A\times X_B\to\mathrm{Prop}\), and residual
5398: \(\delta:X_A\times X_B\to D\).  Define
5399: \begin{align*}
5400:   \mathcal O_U
5401:   &:=
5402:   \{((a,b),(a',b')) :
5403:      q_A(a)=q_A(a'),\ q_B(b)=q_B(b'),\\
5404:   &\hspace{7em}
5405:      q_{AB}(U(a,b))\ne q_{AB}(U(a',b'))\},\\
5406:   \mathcal O_{\delta}
5407:   &:=
5408:   \{((a,b),(a',b')) :
5409:      q_A(a)=q_A(a'),\ q_B(b)=q_B(b'),\
5410:      \delta(a,b)\ne\delta(a',b')\}.
5411: \end{align*}
5412: Write \(\operatorname{COD}\) and \(\operatorname{CRD}\) for
5413: composite-outcome descent and cross-residual descent.  Then
5414: \begin{align*}
5415:   \operatorname{COD}
5416:   &\iff
5417:   \mathcal O_U=\emptyset
5418:   \iff
5419:   \exists\,\bar U:Q_A\times Q_B\to Q_{AB},\
5420:     \bar U(q_Aa,q_Bb)=q_{AB}(U(a,b)),\\
5421:   \operatorname{CRD}
5422:   &\iff
5423:   \mathcal O_{\delta}=\emptyset,\\
5424:   \operatorname{Composable}
5425:   &\iff
5426:   \begin{gathered}
5427:     \operatorname{Adm}\ \text{descends}\wedge
5428:     \operatorname{COD}\\
5429:     {}\wedge\operatorname{CRD}
5430:     \wedge\operatorname{Assoc}\wedge\operatorname{Id}.
5431:   \end{gathered}
5432: \end{align*}
5433: \end{theorem}
5434: \footnote{\raggedright Verified in Lean as
5435: \texttt{StatusRecordsCoherence.Composability.composability}; see
5436: \Cref{app:formalization}.}
5437: \begin{proof}
5438: Assume the component quotients \(q_A,q_B\), interface readouts
5439: \(\beta_A,\beta_B\), composition \(U\), composite quotient
5440: \(q_{AB}\), admissibility predicate \(\operatorname{Adm}\), and
5441: residual \(\delta\).  The composite outcome descends exactly when it
5442: is independent of representatives of the \(Q_A\)- and \(Q_B\)-classes.
5443: Thus, if \(\mathcal O_U=\emptyset\), the definition
5444: \[
5445:   \bar U(q_Aa,q_Bb):=q_{AB}(U(a,b))
5446: \]
5447: is well-defined; if \(\mathcal O_U\ne\emptyset\), a displayed pair in
5448: \(\mathcal O_U\) is precisely a split-pair obstruction.
5449: 
5450: The same argument applied to \(\delta\) gives cross-residual descent.
5451: There are two cases.  If admissibility, outcome descent, residual
5452: descent, associativity, and identity all hold, the chained
5453: \(\BirdInt\) audits compose and \Cref{thm:F20} forms the composite
5454: record.  If any one of these conditions fails, either the composite is
5455: not well-defined on quotient classes or the audit chain is invalid, so
```
