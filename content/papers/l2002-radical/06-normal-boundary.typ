#import "defs.typ": *

В соответствии с введенными в начале параграфа обозначениями будем рассматривать
множества (а)–(г) из леммы @lem:l2002-radical-lie-generating-subgroups как
подгруппы присоединенной группы; подгруппа $H_0$ из доказательства предыдущей
леммы используется вместо множества @eq:l2002-radical-lie-basic-subgroup. Кроме
того, сопоставим с каждой матрицей $lr(‖a_(s t)‖) in R$ следующие множества:
$
  P_(i j) lr((T)), quad P_(1 j) lr((J T)), quad P_(i n) lr((J T))
  quad "при" i > j comma a_(i i) compose a^*_(j j) ∉ J T;
$ <eq:l2002-radical-normal-diagonal-t>
$
  P_(i j) lr((J T)), quad "если" J(a_(i i) compose a^*_(j j)) ⊈ J^2 T
  "или" i > j comma a_(i i) compose a^*_(j j) ∉ J^2 T;
$ <eq:l2002-radical-normal-diagonal-jt>
$
  K(a_(i j)e_(i,j-1) + a^*_(j-1,i+1)e_(j,i+1)
    + a_(i+1,j)e_(i+1,j-1) + a^*_(j-1,i)e_(j i)), quad
  K(a_(i j)e_(i+1,j) + a^*_(j-1,i+1)e_(j-1,i)
    + a_(i,j-1)e_(i+1,j-1) + a^*_(j,i+1)e_(j i)), quad
  K(a_(i j)e_(i+1,j-1) + a_(j-1,i+1)e_(j i))
  quad ((i, j) in Lc comma (j - 1, i + 1) in Lc');
$ <eq:l2002-radical-normal-coupled-corners>
$
  K(a_(i j)e_(i,j-1) + a^*_(j-1,m)e_(j m))
  quad ((i, j) comma (j - 1, m) in Lc union Lc' comma
    m != i + 1 comma (i, m) != (n, 1));
$ <eq:l2002-radical-normal-adjacent-corners>
$
  K(a_(n j)e_(n,j-1) + a^*_(j-1,1)e_(j 1)
    + a_(1 j)e_(1,j-1) + a^*_(j-1,n)e_(j n)), quad
  J(a_(n j)e_(1 j) + a^*_(j-1,1)e_(j-1,n)
    + a_(n,j-1)e_(1,j-1) + a^*_(j 1)e_(j n)), quad
  J(a_(n j)e_(1,j-1) + a_(j-1,1)e_(j n))
  quad ((n, j) comma (j - 1, 1) in Lc);
$ <eq:l2002-radical-normal-border-coupled-corners>
$
  J(a_(n j)e_(1 j) + a^*_(i 1)e_(i n))
  quad ((n, j) comma (i, 1) in Lc comma i != j - 1).
$ <eq:l2002-radical-normal-border-separated-corners>

#lemma[
  Нормальная подгруппа $H$ присоединенной группы кольца $R$ содержит подгруппы
  (а)–(г) из леммы~@lem:l2002-radical-lie-generating-subgroups и, кроме того,
  для любой матрицы $lr(‖a_(s t)‖) in H$ множества
  @eq:l2002-radical-normal-diagonal-t–@eq:l2002-radical-normal-border-separated-corners.
] <lem:l2002-radical-normal-generating-subgroups>

Доказательство является несложным перенесением доказательства леммы
@lem:l2002-radical-lie-generating-subgroups, и мы его опускаем.

Как и в §~@sec:l2002-radical-boundaries, определяем множества $tilde(Lc)$,
$tilde(Lc)'$, а по формулам @eq:l2002-radical-enlarged-support определены также
подгруппы $tilde(B)$ и $D$ присоединенной группы кольца $R$.

#lemma[
  $H$ совпадает с нормальным замыканием пересечения $H inter (tilde(B) + D)$, а
  как подгруппа присоединенной группы порождается подгруппами (а)–(г) из
  леммы~@lem:l2002-radical-lie-generating-subgroups, $H_0$,
  $H inter (tilde(B) + D)$ и множествами
  @eq:l2002-radical-normal-diagonal-t–@eq:l2002-radical-normal-border-separated-corners
  для всевозможных матриц $lr(‖a_(s t)‖) in H$. Кроме того, пересечение
  $H inter (tilde(B) + D)$ является нормальной $T$-границей в кольце $R$.
] <lem:l2002-radical-normal-boundary-existence>

#proof[
  Пусть $beta = lr(‖b_(s t)‖) in H$. Все недиагональные проекции $H_(u v)$ и,
  следовательно, $b_(u v)$ ($u != v$), лежат в $T$, $J T$ или $J^2 T$ в
  соответствии с их описанием в
  лемме~@lem:l2002-radical-normal-corner-classification. По аналогии с
  доказательством леммы~@lem:l2002-radical-lie-reduction будем аннулировать
  недиагональные элементы на позициях $(u, v) ∉ tilde(Lc) union tilde(Lc)'$.
  Вначале рассмотрим позиции $(u, v)$, перечисленные в пп. (а)–(в)
  доказательства леммы~@lem:l2002-radical-lie-reduction. Умножением
  (присоединенным) $beta$ на подходящую матрицу из множеств
  @eq:l2002-radical-normal-coupled-corners–@eq:l2002-radical-normal-border-separated-corners
  аннулируем по модулю $J^2 T$ коэффициенты $b_(u v)$ для всевозможных позиций
  $(u, v)$ из пп. (а), (в) и для позиций $(u, v) ⋡ Lc$ из п. (б). Используя
  также множества @eq:l2002-radical-normal-adjacent-corners и первое множество
  из @eq:l2002-radical-normal-border-coupled-corners, аннулируем по модулю $J T$
  коэффициенты $b_(u v)$ для оставшихся позиций $(u, v)$ из п. (б).

  Очевидно, найденные условия для перечисленных позиций не изменяются, если
  использовать умножения слева на элементарные матрицы из множеств (а)–(г)
  леммы~@lem:l2002-radical-lie-generating-subgroups в $H$ и из $H_0$:
  $-b_(u v)e_(u v) compose beta = -b_(u v)e_(u v) + beta
  - b_(u v)sum_j b_(v j)e_(u j)$. С другой #source(18, printed: 436)стороны,
  такие умножения позволяют аннулировать по модулю $J T$ недиагональные
  коэффициенты на позициях $(u, v) ∉ tilde(Lc) union tilde(Lc)'$, $(u, v) ≻ Lc$;
  умножения проводим последовательно: вначале для позиций из $j_r$-го столбца,
  затем $(j_r - 1)$-го, …, 1-го столбцов, см. @eq:l2002-radical-primary-corners
  и (@fig:l2002-radical-corner-matrix).

  Отметим, что после указанных преобразований $beta$ ее диагональные
  коэффициенты на позициях $(u, u)$ не изменяются по модулю $J T$ при $u >= i_1$
  (в обозначениях @eq:l2002-radical-primary-corners) и не изменяются по модулю
  $J^2 T$ при $u < i_1$.

  Будем аналогично аннулировать недиагональные элементы на позициях
  $(u, v) ∉ tilde(Lc) union tilde(Lc)'$ по модулю $J^2 T$. При этом используем
  умножения слева только на элементарные матрицы $-a_(u v)e_(u v)$ из множеств
  (б)–(г) леммы~@lem:l2002-radical-lie-generating-subgroups в $H$ и из $H_0$,
  причем рассматриваем последовательно случаи $v = n, n - 1, dots, 1$. Кроме
  того, если в $v$-м столбце встречается угол $(k, v)$ из $Lc$, то добавку из
  $J T$ к коэффициенту $a_(k v)$, возможную на предыдущем этапе, аннулируем по
  модулю $J^2 T$, пользуясь включением $H supset P_(k v) lr((J T))$ из леммы
  @lem:l2002-radical-normal-primary-subgroups (г), (д). Заметим также, что
  диагональные коэффициенты матрицы, полученной на предыдущем этапе, не
  изменились по модулю $J^2 T$.

  Включение $P_(1 n) lr((J^2 T)) subset H$ позволяет далее аналогично
  аннулировать недиагональные элементы на позициях
  $(u, v) ∉ tilde(Lc) union tilde(Lc)'$ по модулю $J^3 T$, и т. д. В силу
  нильпотентности идеала $J$ матрица $beta$ через конечное число шагов
  преобразуется к матрице $gamma in H inter (tilde(B) + D)$. Коэффициенты
  матрицы $beta$ на позициях $(u, v) in Lc union Lc'$ остаются без изменений, а
  ее диагональные коэффициенты $b_(u u)$ не изменяются по модулю $J T$ при
  $u >= i_1$ и не изменяются по модулю $J^2 T$ при $u < i_1$.

  Таким образом, множества @eq:l2002-radical-normal-diagonal-t–
  @eq:l2002-radical-normal-border-separated-corners для всевозможных матриц
  $lr(‖a_(s t)‖) in H$ и подгруппы (а)–(г) из леммы
  @lem:l2002-radical-lie-generating-subgroups, $H_0$ и $H inter (tilde(B) + D)$
  порождают произвольную матрицу $beta$ из $H$, а следовательно, порождают $H$
  как подгруппу присоединенной группы.

  Как и в доказательстве леммы~@lem:l2002-radical-lie-boundary-existence,
  множество $A = H inter (tilde(B) + D)$ удовлетворяет условиям
  @cond:l2002-radical-boundary-degeneracy–@cond:l2002-radical-lie-support.
  Множества @eq:l2002-radical-normal-coupled-corners–
  @eq:l2002-radical-normal-border-separated-corners для всевозможных
  $lr(‖a_(s t)‖) in H$, кроме последних множеств в
  @eq:l2002-radical-normal-coupled-corners и
  @eq:l2002-radical-normal-border-coupled-corners, и подгруппы $H_0$, (а)–(г) из
  леммы~@lem:l2002-radical-lie-generating-subgroups полностью определяются
  множеством углов $Lc$, $Lc'$, и по построению все они лежат в нормальном
  замыкании множества $A$. Последнее включение выполняется и для исключительных
  множеств в @eq:l2002-radical-normal-coupled-corners и
  @eq:l2002-radical-normal-border-coupled-corners; это несложно устанавливается
  перенесением соответствующего доказательства
  леммы~@lem:l2002-radical-lie-boundary-existence.

  Допустим, что для матрицы $beta$ имеем $b_(u u) compose b^*_(v v) ∉ J^k T$; в
  этом случае будем говорить, что $beta$ удовлетворяет
  $((u, v), J^k T)$-условию. Рассмотрим случай, когда $k = 1$ и, следовательно,
  множества $P_(i j) lr((T))$, $P_(1 j) lr((J T))$ и $P_(i n) lr((J T))$ из
  @eq:l2002-radical-normal-diagonal-t по лемме
  @lem:l2002-radical-normal-generating-subgroups лежат в $H$. Используем
  отмеченное выше свойство диагональных элементов матрицы $beta$ при ее
  преобразовании к матрице $gamma$ из $A$. Нетрудно убедиться, что либо $gamma$
  также удовлетворяет $((u, v), J T)$-условию, либо указанные множества входят
  уже в подгруппу $H_0$ из $H$ в силу описания $H_0$. Исследуя аналогично
  $((u, v), J^2 T)$-условие матриц из $H$, устанавливаем включение множеств
  @eq:l2002-radical-normal-diagonal-t и @eq:l2002-radical-normal-diagonal-jt в
  нормальное замыкание множества $A$; это завершает доказательство равенства $H$
  и нормального замыкания множества $A$ в присоединенной группе. Вместе с тем
  получаем справедливость свойств @cond:l2002-radical-normal-diagonal-jt и
  @cond:l2002-radical-normal-diagonal-jjt для $A$.

  Сейчас очевидно, что если $A subset A_1 subset tilde(B) + D$ и нормальное
  замыкание множества $A_1$ совпадает с $H$, то
  $A_1 subset H inter (tilde(B) + D) = A$ и $A_1 = A$. Поэтому условие
  @cond:l2002-radical-normal-maximality для $A$ также выполняется и $A$ является
  нормальной $T$-границей. Лемма доказана.
]

В доказательстве леммы~@lem:l2002-radical-normal-boundary-existence установлена
также

#lemma[
  #source(19, printed: 437)Пусть $A = A lr((T; Lc, Lc'))$ — произвольная
  нормальная $T$-граница кольца $R$. Тогда минимальная нормальная подгруппа
  присоединенной группы $R$, содержащая $A$, порождается как присоединенная
  группа множествами $A$, $H_0$, (а)–(г) из леммы
  @lem:l2002-radical-lie-generating-subgroups и еще множествами
  @eq:l2002-radical-normal-diagonal-t–@eq:l2002-radical-normal-border-separated-corners
  для всевозможных матриц $lr(‖a_(s t)‖) in A$.
] <lem:l2002-radical-normal-boundary-generators>

Теорема~@th:l2002-radical-normal-boundary легко следует из лемм
@lem:l2002-radical-normal-corner-classification и
@lem:l2002-radical-normal-boundary-existence.
