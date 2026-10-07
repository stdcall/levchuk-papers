#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": NT, proposition

=== <sec:l1987-rings-automorphism-types>

Заметим, что $Aut R = Aut cal(G)(R) inter Aut Lambda(R)$, $R = NT(Gamma, K)$.
Выделим основные автоморфизмы. Кольцевые автоморфизмы индуцируются, как и
обычно, автоморфизмами кольца $K$. Сдвиг
$x epsilon_(i j) arrow.r x epsilon_(i' j')$ ($x in K$, $i > j$) индуцируется
автоморфизмом $i arrow.r i'$ цепи $Gamma$. Для произвольного антиавтоморфизма
$theta$ кольца $K$ и антиавтоморфизма цепи $Gamma$ отображение
$x epsilon_(i j) arrow.r -x^theta epsilon_(j' i')$ ($x in K$, $i > j$)
определяет автоморфизмы группы $cal(G)(R)$ и кольца $Lambda(R)$ (подчеркнем, что
продолжения на $cal(G)(R)$ и $Lambda(R)$ не совпадают); их называем
_антисдвигами_.

Пусть $p, q in Gamma$ и, следовательно, центр кольца $R$ равен
$K epsilon_(q p)$. Произвольный центральный автоморфизм получим, полагая
$x epsilon_(i j) arrow.r x epsilon_(i j) + x^(lambda_j) epsilon_(q p)$,
$x in K$, для всех $i, j in Gamma$, $j ◁ i$ (остальные элементы
$x epsilon_(u v)$ неподвижны), где $lambda_j$ — эндоморфизмы аддитивной группы
$K^+$ кольца $K$. Если существует $k in Gamma$, $p ◁ k < q$, то преобразованию
$lambda$ кольца $K$ с условием

$
  (x+y)^lambda = x^lambda + y^lambda + a x y quad (x, y in K),
  quad a = 2^lambda - 2(1^lambda),
$

#source(7, printed: 636) соответствует автоморфизм

$
  sigma_lambda: x epsilon_(k p) arrow.r (epsilon_(k p) + a epsilon_(q k))x
  + x^lambda epsilon_(q p) quad (x in K)
$

группы $cal(G)(R)$ (конечно, при $2K = 0$ это центральный автоморфизм).
Автоморфизм

$
  sigma_a: x epsilon_(k p) arrow.r (epsilon_(k p) + a epsilon_(q k))x
  quad (x in K)
$

кольца $Lambda(R)$ определен для любого $a in K$ с условием $a(K*K) = 0$. Если
$p ◁ k ◁ t < q$, то, как и в [@bib:l1987-rings-Levchuk1983, §
@sec:l1983-elementary], определен автоморфизм $nu_a$ кольца $Lambda(R)$ при
$a in K$, $a(K*K) = 2a = 0$, и автоморфизм $eta_a$ группы $cal(G)(R)$ при тех же
условиях и, кроме того,

$ a(x^2-x)(y^2-y) = 0 quad (x, y in K). $

В частности:

$
  nu_a: x epsilon_(k p) arrow.r (epsilon_(k p)+a epsilon_(q t))x,
  quad x epsilon_(t p) arrow.r (epsilon_(t p)+a epsilon_(q k))x quad (x in K).
$

Как и в [@bib:l1987-rings-Levchuk1983, § @sec:l1983-elementary], симметрично
определяются автоморфизмы $sigma'_b$ (здесь $(K*K)b = 0$) и $sigma'_lambda$ при
$p < m ◁ q$, а также $nu'_b$ и $eta'_b$ при $p < s ◁ m ◁ q$. Элементы подгруппы,
порожденной всевозможными автоморфизмами $sigma_lambda$, $sigma'_lambda$,
$eta_a$, $eta'_b$ группы $cal(G)(R)$ (аналогично, автоморфизмами $sigma_a$,
$sigma'_b$, $nu_a$, $nu'_b$ кольца $Lambda(R)$), называем _гиперцентральными_
автоморфизмами.

Диагональный автоморфизм $alpha arrow.r delta alpha delta^(-1)$ ($alpha in R$)
кольца $R$ определен для любой диагональной обратимой $Gamma$-матрицы $delta$
над $K$. Пусть $beta = ‖b_(u v)‖$, $beta' = ‖b'_(u v)‖$ — матрицы над $K$, у
которых в каждой строке с номером $!= q$ (при $q in Gamma$) и в каждом столбце с
номером $!= p$ имеется лишь конечное число ненулевых элементов,
$b_(i j) = b'_(i j) = 0$ ($i <= j$), причем $(i,j)$-координаты произведений
$(1+beta)(1+beta')$, $(1+beta')(1+beta)$ при $i > j$, $(i,j) != (q,p)$ равны
$0$. Тогда $alpha arrow.r (1+beta) alpha (1+beta')$ ($alpha in R$) — автоморфизм
кольца $R$, который на каждом конечном множестве действует как внутренний
автоморфизм. Такой автоморфизм называют _локально внутренним_
[@bib:l1987-rings-Gorchakov1978].
