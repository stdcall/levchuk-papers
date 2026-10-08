#import "defs.typ": *
#import "diagrams/corners.typ": corners-diagram

=== $T$-границы кольца $R_n lr((K, J))$ <sec:l2002-radical-boundaries>

Множество $H_(k m) = {a_(k m) | lr(‖a_(s t)‖) in H}$, обозначаемое также через
$pi_(k m) lr((H))$, назовем $(k, m)$-проекцией произвольного множества $H$
матриц. Через $e_(u v)$ будем обозначать $n times n$-матрицу, у которой
$(u, v)$-проекция равна единице, а остальные проекции нулевые (матричная
единица).

Как и в [@bib:l2002-radical-Kuzucuoglu2000; § @sec:l2000-ideals-construction],
будем использовать частичный порядок $≽$ на множестве матричных позиций, полагая
$(u, v) ≽ (k, m)$, когда $u >= k$, $v <= m$; если еще $(u, v) != (k, m)$, то
пишем $(u, v) ≻ (k, m)$. Для множества $Lc$ матричных позиций полагаем также
$(u, v) ≽ Lc$, если $(u, v) ≽ (k, m)$ хотя бы для одной позиции $(k, m) in Lc$;
конечно, при $Lc = emptyset$ позиций $(u, v)$ с таким условием не существует.
_Множеством углов степени_ $n$ называем пару $Lc$, $Lc'$ множеств матричных
позиций вида
$
  Lc = {(i_1, j_1), (i_2, j_2), dots, (i_r, j_r)}, quad r >= 1,
$ <eq:l2002-radical-primary-corners>
$
  1 <= j_1 < j_2 < dots < j_r <= n,
  quad 1 <= i_1 < i_2 < dots < i_r <= n;
$
$
  Lc' = {(k_1, m_1), (k_2, m_2), dots, (k_q, m_q)}, quad q >= 0,
$ <eq:l2002-radical-secondary-corners>
$
  j_r < m_1 < m_2 < dots < m_q <= n,
  quad 1 <= k_1 < k_2 < dots < k_q < i_1.
$
Очевидно, множество углов не содержит двух матричных позиций из одной строки или
одного столбца, а также сравнимых позиций $(u, v) ≻ (k, m)$, лежащих
одновременно либо в $Lc$, либо в $Lc'$.

Пусть $T$ — какой-либо $J$-подмодуль кольца $K$. Согласно
[@bib:l2002-radical-Kuzucuoglu2000; § @sec:l2000-ideals-construction]
$T$-границей кольца $R_n lr((K, J))$ называется любая его аддитивная подгруппа
$A$, для которой существует множество углов $(Lc, Lc')$ со следующими условиями:

#condition[
  $J B subset A subset B = sum_((i,j) in Lc) T e_(i j)
  + sum_((k,m) in Lc') (J T)e_(k m)$;
] <cond:l2002-radical-boundary-support>
#condition[
  $Lc' = emptyset$ при $J T = J^2 T$ и $Lc = {(1, n)}$ при $J T = T$;
] <cond:l2002-radical-boundary-degeneracy>
#condition[
  $pi_(n 1) lr((A)) = T$ при $Lc = {(n, 1)}$, а в остальных случаях идеал
  $K pi_(i j) lr((A))$ совпадает с $T$ при всех $(i, j) in Lc$ и с $J T$ при
  всех $(i, j) in Lc'$.
] <cond:l2002-radical-boundary-projections>

#source(3, printed: 421)Идеал кольца $R_n lr((K, J))$, порожденный $T$-границей
$A = A(T; Lc, Lc')$, записывается явно в виде
$
  A + sum_((i,j) ≻ Lc) T e_(i j)
  + sum_((k,m) ≻ Lc') (J T)e_(k m)
  + sum_((k,m) ≽ {(1,j_r),(i_1,n)}) (J T)e_(k m)
  + sum_((k,m) ≽ (1,n)) (J^2 T)e_(k m)
$
и представляется наглядно с использованием формальной $n times n$-матрицы

#corners-diagram <fig:l2002-radical-corner-matrix>

Оказывается [@bib:l2002-radical-Kuzucuoglu2000; теорема
@th:l2000-ideals-boundary-classification], что при условии сильной
максимальности идеала $J$ в кольце $K$ любой идеал кольца $R_n lr((K, J))$
порождается подходящей $T$-границей. Более точно, справедлива (см.
[@bib:l2002-radical-Kuzucuoglu2000, теорема
@th:l2000-ideals-boundary-classification])

#theorem[
  Пусть $H$ — произвольный идеал кольца $R_n lr((K, J))$, $n >= 2$, и $T$ — его
  $(n, 1)$-проекция. Если $J$ — сильно максимальный идеал кольца $K$, то
  существует и единственна $T$-граница $A = A(T; Lc, Lc')$ кольца
  $R_n lr((K, J))$, порождающая $H$, причем $A = H inter B$.
] <th:l2002-radical-associative-boundary>

Для подобного описания нормальных подгрупп присоединенной группы кольца
$R_n lr((K, J))$ и идеалов ассоциированного кольца Ли ниже вводятся понятия
_нормальной_ и _лиевой_ $T$-границ.

Кольцо $R_n lr((K, J))$ порождается аддитивными подгруппами вида $K e_(v,v-1)$ и
$J e_(1 n)$. Для выявления лиевой замкнутости его подмножеств используем понятия
связанных углов. Угол $(u, v)$ назовем _право- (лево-) связанным_, если
$Lc union Lc'$ содержит угол в $(v - 1)$-й строке (соответственно в $(u + 1)$-м
столбце) или $Lc$ содержит угол в $n$-й строке и $v = 1$ (соответственно, в 1-м
столбце и $u = n$).

Множеству углов $(Lc, Lc')$ будем сопоставлять множества $tilde(Lc)$,
$tilde(Lc)'$ матричных позиций. Множество $tilde(Lc)'$ получаем присоединением к
$Lc'$ следующих позиций:

$(v, t)$, если $(v - 1, t)$ — угол из $Lc'$, лево-связанный с углом из $Lc'$;

$(i, n)$, если $(i, 1)$ — право-связанный угол в $Lc$, и еще позиция
$(i + 1, n)$, когда $(i, 1) in Lc$ и $(n, i + 1) in Lc$.

Множество $tilde(Lc)$ получается из $Lc$ присоединением позиций:

$(v, t)$, если $(v - 1, t)$ — лево-связанный угол в $Lc$ или $(v, t + 1)$ — угол
из $Lc$, право-связанный с углом из $Lc'$;

$(u + 1, v)$, $(u, v - 1)$ и $(u + 1, v - 1)$, когда $(u, v) in Lc$ и
$(v - 1, u + 1) in Lc'$.

Положим
$
  tilde(B) = tilde(B)(T; Lc, Lc')
  = sum_((i,j) in tilde(Lc)) T e_(i j)
  + sum_((k,m) in tilde(Lc)') (J T)e_(k m),
  quad D = sum_(u=1)^n J e_(u u).
$ <eq:l2002-radical-enlarged-support>

#definition[
  #source(4, printed: 422)Аддитивная подгруппа $A$ кольца $R_n lr((K, J))$
  называется его _лиевой_ $T$-границей, если существует множество углов
  $(Lc, Lc')$, которое не содержит позиций главной диагонали, удовлетворяет
  условиям @cond:l2002-radical-boundary-degeneracy,
  @cond:l2002-radical-boundary-projections и следующим условиям:

  #condition[
    $J tilde(B) subset A subset tilde(B) + D$;
  ] <cond:l2002-radical-lie-support>
  #condition[
    если $lr(‖a_(s t)‖) in A$ и $1 <= v < u <= n$, то
    $K(a_(u u) - a_(v v)) subset T$ и при $a_(u u) != a_(v v) mod J T$ имеем
    $(u, v) ≽ Lc$ и $(v, u) ≽ Lc'$, причем $T e_(u v) subset A$,
    $J T e_(u n) subset A$, $J T e_(u+1,n) subset A$ и $J T e_(v u) subset A$
    соответственно случаям $(u, v) in tilde(Lc)$, $(u, n) in tilde(Lc)'$,
    $(u + 1, n) in tilde(Lc)'$ и $(v, u) in tilde(Lc)'$;
  ] <cond:l2002-radical-lie-diagonal-jt>
  #condition[
    если $lr(‖a_(s t)‖) in A$, $1 <= v < u <= n$ и
    $a_(u u) != a_(v v) mod J^2 T$, то $(u, v) ≽ Lc'$, причем
    $J T e_(u v) subset A$, когда $(u, v) in tilde(Lc)'$;
  ] <cond:l2002-radical-lie-diagonal-jjt>
  #condition[
    если $A subset A_1 subset tilde(B) + D$ и лиевы идеалы в $R_n lr((K, J))$,
    которые порождают $A$ и $A_1$, совпадают, то $A = A_1$.
  ] <cond:l2002-radical-lie-maximality>
] <def:l2002-radical-lie-boundary>

В терминах введенных лиевых $T$-границ кольца $R_n lr((K, J))$ описание его
лиевых идеалов по аналогии с теоремой~@th:l2002-radical-associative-boundary
устанавливает основная в §~@sec:l2002-radical-lie-ideals
теорема~@th:l2002-radical-lie-boundary. Понятие лиевой $T$-границы, по существу,
вводится уже в [@bib:l2002-radical-Suleimanova2000b], однако без условия
@cond:l2002-radical-lie-maximality. С другой стороны, как выявляется в
§~@sec:l2002-radical-lie-ideals, именно условие
@cond:l2002-radical-lie-maximality обеспечивает утверждение единственности в
теореме~@th:l2002-radical-lie-boundary и позволяет заменить требование
аддитивности лиевой $T$-границы $A$ в
определении~@def:l2002-radical-lie-boundary условием $A subset R_n lr((K, J))$.

Присоединенное умножение $a compose b = a + b + a b$ в ассоциативном кольце
всегда является полугрупповой операцией. Кольцо называют _радикальным_, если
присоединенное умножение — групповая операция. Известно
[@bib:l2002-radical-Kuzucuoglu2000; § @sec:l2000-ideals-structural], что условие
радикальности кольца $R_n lr((K, J))$ равносильно квазирегулярности идеала $J$,
т.~е. $(J, compose)$ — группа. В этом случае отображение
$alpha arrow.r e + alpha$ присоединенной группы кольца $R_n lr((K, J))$ ($e$ —
единичная матрица) является ее мономорфизмом в $GL_n lr((K))$.

#lemma(title: [см. [@bib:l2002-radical-Levchuk1976, теорема
  @th:l1976-normal-lie-correspondence]])[
  Лиевы идеалы кольца $NT_n lr((K)) = R_n lr((K, 0))$, и только они, являются
  нормальными подгруппами присоединенной группы. В частности, для всякой
  нормальной подгруппы $H$ присоединенной группы кольца $R_n lr((K, J))$
  пересечение $H inter NT_n lr((K))$ будет подкольцом и лиевым идеалом кольца
  $NT_n lr((K))$.
] <lem:l2002-radical-niltriangular-normal-lie>

Как показывает теорема @th:l1976-normal-lie-correspondence из
[@bib:l2002-radical-Levchuk1976], при условии $1 in K$ или даже при более слабом
условии $K = K^2$ на ассоциативное кольцо $K$ класс всех нормальных подгрупп
присоединенной группы кольца $NT_n lr((K))$ совпадает с классом всех идеалов
ассоциированного кольца Ли. (Существенность условия $K = K^2$ показывает пример
@exm:l1976-even-ring из [@bib:l2002-radical-Levchuk1976]). Вопрос о
характеризации радикальных колец с отмеченным структурным соответствием записан
в [@bib:l2002-radical-Kourovka1992, вопрос 10.19] и остается открытым.
Оказывается, для радикальных колец $R_n lr((K, J))$ (с коммутативным кольцом
$K$), $n >= 2$, случай $J = 0$ является единственным, когда указанное
структурное соответствие выполняется. Это показывает следующий, предложенный
вторым автором пример.

#example[
  Подмножество $M$ всех матриц со следом 0 в кольце $R_n lr((K, J))$, очевидно,
  будет лиевым идеалом. Однако $M$ не является даже подгруппой присоединенной
  группы, если $J != 0$. Действительно, при ненулевом $y in J$ присоединенное
  произведение $e_21 compose y e_12 = e_21 + y e_12 + y e_22$ матриц из $M$
  имеет ненулевой след, равный $y$, и поэтому не лежит в $M$.
] <exm:l2002-radical-trace>

Ранее в [@bib:l2002-radical-Kuzucuoglu2000, пример
@exm:l2000-ideals-determinant-kernel] уже показывалось, что для радикальных
колец $R_n lr((K, J))$, $n >= 2$, указанное структурное соответствие нарушается,
если кольцо $K$ коммутативно, а идеал $J$ содержит элемент с ненулевым
квадратом.

#source(5, printed: 423)Конечно, для описания нормальных подгрупп присоединенной
группы кольца $R_n lr((K, J))$ поиски аналога
теоремы~@th:l2002-radical-lie-boundary целесообразны, лишь когда кольцо
$R_n lr((K, J))$ радикально. Элемент, квазиобратный к $alpha$, обозначаем через
$alpha'$, так что $alpha compose alpha' = alpha' compose alpha = 0$. При
$alpha = lr(‖a_(s t)‖)$ полагаем $alpha' = lr(‖a_(s t)^ast‖)$.

#definition[
  Подмножество $A$ радикального кольца $R_n lr((K, J))$ называется его
  _нормальной_ $T$-границей, если существует множество углов $(Lc, Lc')$,
  которое не содержит позиций главной диагонали, удовлетворяет условиям
  @cond:l2002-radical-boundary-degeneracy– @cond:l2002-radical-lie-support и
  следующим условиям:

  #primed-condition([@cond:l2002-radical-lie-diagonal-jt])[
    если $lr(‖a_(s t)‖) in A$ и $1 <= v < u <= n$, то
    $K(a_(u u) compose a_(v v)^ast) subset T$ и при
    $a_(u u) compose a_(v v)^ast in.not J T$ имеем $(u, v) ≽ Lc$ и
    $(v, u) ≽ Lc'$, причем $T e_(u v) subset A$, $J T e_(u n) subset A$,
    $J T e_(u+1,n) subset A$ и $J T e_(v u) subset A$ соответственно случаям
    $(u, v) in tilde(Lc)$, $(u, n) in tilde(Lc)'$, $(u + 1, n) in tilde(Lc)'$ и
    $(v, u) in tilde(Lc)'$;
  ] <cond:l2002-radical-normal-diagonal-jt>
  #primed-condition([@cond:l2002-radical-lie-diagonal-jjt])[
    если $lr(‖a_(s t)‖) in A$, $1 <= v < u <= n$ и
    $a_(u u) compose a_(v v)^ast in.not J^2 T$, то $(u, v) ≽ Lc'$, причем
    $J T e_(u v) subset A$, когда $(u, v) in tilde(Lc)'$;
  ] <cond:l2002-radical-normal-diagonal-jjt>
  #primed-condition([@cond:l2002-radical-lie-maximality])[
    если $A subset A_1 subset tilde(B) + D$ и нормальные замыкания подмножеств
    $A$ и $A_1$ в присоединенной группе кольца $R_n lr((K, J))$ совпадают, то
    $A = A_1$.
  ] <cond:l2002-radical-normal-maximality>
] <def:l2002-radical-normal-boundary>

Основная в §~@sec:l2002-radical-normal-subgroups
теорема~@th:l2002-radical-normal-boundary дает описание нормальных подгрупп
присоединенной группы кольца $R_n lr((K, J))$ в терминах нормальных $T$-границ.
