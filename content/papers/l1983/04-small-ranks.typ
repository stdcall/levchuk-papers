#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

=== Автоморфизмы при малых $n$ <sec:l1983-small-ranks>

В леммах~@lem:l1983-rank-four-adjoint-decomposition,
@lem:l1983-rank-four-lie-decomposition не выясняется, при каких условиях на
матрицу $lr(‖c_(i j)‖)$ (в терминах ее элементов) существуют автоморфизмы вида
@eq:l1983-rank-four-adjoint-map и @eq:l1983-rank-four-lie-map. Для
коммутативного кольца $K$ указанные автоморфизмы также можно разложить в
произведение «элементарных автоморфизмов», описав тем самым полностью группы
$Gc_4 lr((K))$ и $Lambda_4
lr((K))$.

Пусть $K$ — коммутативное кольцо. Тогда условие
@eq:l1983-rank-four-two-annihilation для матрицы $gamma = lr(‖c_(i j)‖)$
совпадает с требованием $2 c_(i 1)c_(i 2) = 0$, $i = 1, 2$. Условие совместности
системы уравнений @eq:l1983-rank-four-inverse-coordinates означает, что $gamma$
— обратимая матрица (обратной к ней является матрица $lr(‖d_(i j)‖)$);
требование @eq:l1983-rank-four-multiplicativity в этом случае равносильно тому,
что $theta$ — автоморфизм кольца $K$. С точностью до умножения автоморфизмов
@eq:l1983-rank-four-adjoint-map, @eq:l1983-rank-four-lie-map на диагональный и
кольцевой автоморфизмы мы можем считать выполненными для них условия
$theta = 1$, $gamma in SL(2, K)$.

Очевидно, что
$
  S^ast = {lr(‖a_(k l)‖) in SL(2, K): 2 a_11 a_12 = 2 a_21 a_22 = 0}
$
есть подгруппа группы $SL(2, K)$. Если $gamma = lr(‖c_(i j)‖) in S^ast$, то
отображение @eq:l1983-rank-four-lie-map с $theta = 1$ определяет эндоморфизм
$overline(gamma)$ лиева кольца $NT(4, K)$, причем #source(
  12,
  printed: 74,
)$overline(gamma) overline(gamma^(-1)) = 1$. Отсюда получаем, что отображение
$gamma arrow.r overline(gamma)$ есть изоморфизм группы $S^ast$ в группу
$Lambda_4 lr((K))$.

Рассмотрим условие @eq:l1983-rank-four-quadratic-condition для матрицы
$gamma = lr(‖c_(i j)‖) in S^ast$. Полагая в нем $y = 1$, приходим к равенству
$
  c_(i 1)c_(i 2)(x^2 - x)(d_(1 i) + d_(2 i)) = c_(i 1)c_(i 2)(x^2 - x),
$
где $lr(‖d_(i j)‖) = gamma^(-1)$. Умножая обе его части на произвольный элемент
$y in K$, получаем равенство, левая часть которого совпадает с левой частью
@eq:l1983-rank-four-quadratic-condition. Следовательно, совпадают и правые части
равенств, т. е. $gamma$ лежит в подгруппе
$
  S = {lr(‖a_(k l)‖) in S^ast: a_(i 1)a_(i 2)(x^2 - x)(y^2 - y) = 0,
    x, y in K, i = 1, 2}
$
группы $S^ast$. С другой стороны, всякая матрица $gamma in S$ удовлетворяет
условию @eq:l1983-rank-four-quadratic-condition, как показывают равенства
$
  (y^2 - y)c_(i 1)c_(i 2)(d_(1 i) + d_(2 i)) =
  (y^2 - y)(c_(i 2)c_11 c_21 + c_(i 1)c_12 c_22)
  (c_11 c_22 - c_12 c_21) = (y^2 - y)c_(i 1)c_(i 2).
$
Как и в лемме~@lem:l1983-rank-four-adjoint-decomposition, отображение
@eq:l1983-rank-four-adjoint-map с $theta = 1$, т. е. отображение
$
  tilde(gamma): quad x epsilon_32 arrow.r x epsilon_32
  + (x^2 - x)(c_11 c_21 epsilon_31 + c_12 c_22 epsilon_42),
  x epsilon_(i'+1,i') arrow.r x(c_(i 1)epsilon_21 + c_(i 2)epsilon_43),
  quad i = 1, 2 quad (1' = 1, 2' = 3),
  x epsilon_(i+2,i) arrow.r (-1)^i x(-c_(i 1)epsilon_31 + c_(i 2)epsilon_42)
  + x^2 c_(i 1)c_(i 2)epsilon_41, quad i = 1, 2,
  x epsilon_41 arrow.r x(c_11 c_22 + c_12 c_21)epsilon_41, quad x in K,
$
при $gamma = lr(‖c_(i j)‖) in S$ определяет эндоморфизм $tilde(gamma)$
присоединенной группы кольца $NT(4, K)$. При этом
$tilde(gamma) tilde(gamma^(-1)) = 1$. Отсюда следует, что отображение
$gamma arrow.r tilde(gamma)$ является изоморфизмом группы $S$ в группу
$Gc_4 lr((K))$. Таким образом, справедлива

#theorem[
  Если $K$ — коммутативное кольцо, то
  $
    Gc_4 lr((K)) = ((Zc Jc Uc^((c))) ⋋ (tilde(S) D)) ⋋ AutK K,
  $
  $
    Lambda_4 lr((K)) = (((Zc Jc) ⋋ Uc^ast) ⋋ (overline(S^ast) D)) ⋋ AutK K.
  $
] <th:l1983-rank-four>

#theorem[
  Пусть $K$ — коммутативное кольцо. Тогда каждая матрица
  $alpha = lr(‖a_(i j)‖) in GL(2, K)$ и преобразования $psi_1$, $psi_2$ кольца
  $K$, удовлетворяющие условию
  $
    (x + y)^(psi_i) = x^(psi_i) + y^(psi_i) + a_(i 1)a_(i 2)x y
    quad (x, y in K), quad i = 1, 2,
  $ <eq:l1983-rank-three-cocycle>
  определяют автоморфизм присоединенной группы кольца $NT(3, K)$ по закону:
  $
    x epsilon_(i+1,i) arrow.r x(a_(i 1)epsilon_21 + a_(i 2)epsilon_32)
    + x^(psi_i)epsilon_31, quad i = 1, 2,
    x epsilon_31 arrow.r (det alpha)x epsilon_31 quad (x in K).
  $ <eq:l1983-rank-three-adjoint-map>
  Если $tilde(Uc)$ — подгруппа таких автоморфизмов, то
  $Gc_3 lr((K)) = tilde(Uc) AutK K$. Отображение
  $
    overline(alpha): quad x epsilon_(i+1,i) arrow.r
    x(a_(i 1)epsilon_21 + a_(i 2)epsilon_32),
    quad x epsilon_31 arrow.r (det alpha)x epsilon_31,
    quad i = 1, 2, x in K,
  $
  определяет автоморфизм лиева кольца $NT(3, K)$ для любой матрицы
  $alpha = lr(‖a_(i j)‖) in GL(2, K)$, причем
  $Lambda_3 lr((K)) = (Zc ⋋ overline(GL)(2, K)) ⋋ AutK K$.
] <th:l1983-rank-three>

#proof[
  Первое утверждение следует из леммы~@lem:l1983-adjoint-extension. Аддитивное
  продолжение на $NT(3, K)$ отображения $overline(alpha)$ есть автоморфизм
  ассоциированного кольца Ли по лемме~@lem:l1983-additive-extension.

  Рассмотрим произвольный автоморфизм $phi in Gc_3 lr((K)) union Lambda_3
  lr((K))$. Действие $phi$ на порождающих элементарных матрицах
  $
    (x epsilon_(i+1,i))^phi = x^(phi_(i 1))epsilon_21
    + x^(phi_(i 2))epsilon_32 + x^(phi_i)epsilon_31
    quad (x in K), quad i = 1, 2,
  $
  #source(13, printed: 75)определяет преобразования $phi_(i j)$, $phi_i$ кольца
  $K$. В силу характеристичности центра $Gamma_2 = K epsilon_31$ и того, что
  операции сложения и присоединенного умножения на $Gamma_2$ совпадают, также
  имеем $(x epsilon_31)^phi = x^(phi_0)epsilon_31$ ($x in K$) для подходящего
  автоморфизма $phi_0$ группы $K^+$. Далее замечаем, что операции лиева
  умножения в кольце $NT(3, K)$ и коммутирования в присоединенной группе
  совпадают. Поэтому соотношения @eq:l1983-elementary-lie-product относительно
  $phi$ сохраняются и, следовательно,
  $
    (x y)^(phi_0) = x^(phi_22)y^(phi_11) - y^(phi_12)x^(phi_21),
    quad x^(phi_(i 2))y^(phi_(i 1)) = y^(phi_(i 2))x^(phi_(i 1))
    quad (x, y in K), quad i = 1, 2.
  $
  Положим $d = 1^(phi_0)$. Используя найденные равенства и условие
  коммутативности кольца $K$, получаем $(x y)^(phi_0)d = x^(phi_0)y^(phi_0)$.
  Так как $K^(phi_0) = K$, то отсюда вытекает, что $d$ — обратимый элемент
  кольца $K$. Поэтому отображение $theta$, определяемое условием
  $a^theta = d^(-1)a^(phi_0)$ ($a in K$), есть автоморфизм группы $K^+$. Более
  того, в силу равенств
  $(a b)^theta = d^(-1)(a b)^(phi_0) = d^(-2)a^(phi_0)b^(phi_0) = a^theta
  b^theta$, $theta$ есть автоморфизм кольца $K$. Далее,
  $
    d x^(phi_12) = 1^(phi_22)1^(phi_11)x^(phi_12)
    - 1^(phi_12)1^(phi_21)x^(phi_12) =
    1^(phi_22)x^(phi_11)1^(phi_12) - x^(phi_12)1^(phi_21)1^(phi_12)
    = x^(phi_0)1^(phi_12), quad x in K,
  $
  откуда $x^(phi_12) = x^theta 1^(phi_12)$. Аналогично находим
  $x^(phi_(i j)) = x^theta 1^(phi_(i j))$ в остальных случаях.

  Положим $alpha = lr(‖1^(phi_(i j))‖)$. Если $phi$ — автоморфизм лиева кольца
  $NT(3, K)$, то, по доказанному, автоморфизм
  $pi = phi overline(alpha)^(-1) overline(theta)^(-1)$ является центральным,
  причем $phi = pi overline(theta) overline(alpha)
  in (Zc ⋋ overline(GL)(2, K)) ⋋ AutK K$. В случае, когда $phi$ — автоморфизм
  присоединенной группы, условие инвариантности соотношений
  @eq:l1983-elementary-addition относительно $phi$ дает
  $
    (x + y)^(phi_i) = x^(phi_i) + y^(phi_i) + x^(phi_(i 2))y^(phi_(i 1))
    quad (x, y in K), quad i = 1, 2.
  $
  Отсюда и в силу равенств $x^(phi_(i j)) = 1^(phi_(i j))x^theta$ матрица
  $alpha = lr(‖1^(phi_(i j))‖)$ и преобразования $psi_i = theta^(-1)phi_i$
  удовлетворяют условию @eq:l1983-rank-three-cocycle и, следовательно,
  определяют автоморфизм $zeta$ по закону @eq:l1983-rank-three-adjoint-map. При
  этом $phi = overline(theta) zeta in tilde(Uc) AutK K$. Теорема доказана.
]
