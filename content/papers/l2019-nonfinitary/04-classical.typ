#import "defs.typ": *

=== #[
  Обобщения нильтреугольных алгебр $N Phi lr((K))$ классических типов
] <sec:l2019-nonfinitary-classical>

#source(7, printed: 45)Алгебру Шевалле над полем $K$ характеризуют системой
корней $Phi$ и базой Шевалле, состоящей из элементов $e_r$ ($r in Phi$) и
подходящей базы подалгебры Картана [@bib:l2019-nonfinitary-Carter1972, § 4.4].
Подалгебру с базой $lr({e_r | r in Phi^+})$ называем _нильтреугольной_ и
обозначаем через $N Phi lr((K))$. Присоединенной группой на ней в
[@bib:l2019-nonfinitary-Levchuk1990] представлена унипотентная подгруппа
$U Phi lr((K))$ группы Шевалле типа $Phi$ над $K$, порождаемая корневыми
автоморфизмами $x_r lr((t))$ ($r in Phi^+,t in K$).

По теореме Шевалле о базисе [@bib:l2019-nonfinitary-Carter1972], при всех
$r,s in Phi^+$ имеем

$
  e_r ast e_s=N_(r,s)e_(r+s)=-e_s ast e_r quad (r+s in Phi),
  quad e_r ast e_s=0 quad (r+s in.not Phi),
$

где структурные константы $N_(r,s)=plus.minus 1,plus.minus 2$ или (для типа
$G_2$) $plus.minus 3$.

Алгебра Ли $N Phi lr((K))$ классического типа представлена в
[@bib:l2019-nonfinitary-Levchuk1990] алгеброй с базой из «матричных единиц»
$e_(i,v)$ с ограничениями на индексы

$
  1<=v<i<=n, quad -i<v<i<=n, quad
  -i<=v<i<=n, v!=0, quad 1<=|v|<i<=n,
$

соответственно типам $A_(n-1),B_n,C_n$ и $D_n$. После соответствующей
перенумерации корней $r=r_(i,v)$ получаем $e_r=e_(i,v)$, причем
$e_(i,j) ast e_(u,v)=0$ при $i!=v,j!=u,j!=-v$. В силу
[@bib:l2019-nonfinitary-Levchuk1990, лемма
@lem:l1990-chevalley-classical-structure-signs], верна

#lemma[
  Знаки структурных констант базиса Шевалле можно выбрать так, что
  $e_(i,j) ast e_(j,v)=e_(i,v)$ и, кроме того,

  $
    Phi=B_n,D_n: quad e_(j,v) ast e_(i,-v)=e_(i,-j)
    quad (i>j>|v|>0);
  $

  $
    Phi=C_n: quad e_(j,m) ast e_(i,-m)=e_(i,m) ast e_(j,-m)=e_(i,-j)
    quad (i>j>m>=1);
  $

  $
    Phi=B_n: quad e_(i,0) ast e_(j,0)=2e_(i,-j), quad
    Phi=C_n: quad e_(i,j) ast e_(i,-j)=2e_(i,-i) quad (i>j>=1).
  $
] <lem:l2019-nonfinitary-chevalley-signs>

Каждый элемент $alpha in N Phi lr((K))$ представляем суммой
$alpha=sum a_(i,v)e_(i,v)$, а также $Phi^+$-матрицей $norm(a_(i,v))$
соответствующего типа. Так, $B_n^+$-матрица имеет вид

$
  mat(
    delim: #none,
    , , a_(1,0), , ;
    , a_(2,-1), a_(2,0), a_(2,1), ;
    dots, dots, dots, dots, dots;
    a_(n,-n+1), dots a_(n,-1), a_(n,0), a_(n,1) dots, a_(n,n-1);
  ).
$

Прямыми вычислениями находим

$
  gamma=norm(c_(i,j))=alpha ast beta
  =lr((sum_(u,v) a_(u,v)e_(u,v))) ast lr((sum_(j,k) b_(j,k)e_(j,k)))
  =sum_(u,v) sum_(j,k) a_(u,v)b_(j,k)(e_(u,v) ast e_(j,k)).
$
<eq:l2019-nonfinitary-expanded-bracket>

#source(8, printed: 46)Укажем формулы умножения $Phi^+$-матриц
$alpha=norm(a_(i,v))$ и $beta=norm(b_(i,v))$ в $N Phi lr((K))$ отдельно для
каждого типа. С учетом @eq:l2019-nonfinitary-expanded-bracket получаем следующие
формулы умножения $B_n^+$-матриц

$
  c_(u,k)=sum_(j=k+1)^(u-1) lr((a_(u,j)b_(j,k)-b_(u,j)a_(j,k))),
  quad 0<=k<u,
$
<eq:l2019-nonfinitary-b-positive>

и, при $k>0$,

$
  c_(u,-k)=2(a_(u,0)b_(k,0)-b_(u,0)a_(k,0))
  +sum_(j=k+1)^(u-1) lr((b_(j,-k)a_(u,j)-a_(j,-k)b_(u,j)))
  +sum_(j>0) lr((a_(k,j)b_(u,-j)-b_(k,j)a_(u,-j)))
  -sum_(j<0) lr((a_(u,-j)b_(k,j)-b_(u,-j)a_(k,j))).
$
<eq:l2019-nonfinitary-b-negative>

#lemma[
  Формулы @eq:l2019-nonfinitary-b-positive и @eq:l2019-nonfinitary-b-negative
  определяют лиево произведение $alpha ast beta=gamma=norm(c_(i,j))$ любых двух
  $B_n$-матриц $alpha=norm(a_(i,j))$ и $beta=norm(b_(i,j))$.
] <lem:l2019-nonfinitary-b-formulas>

Отбрасывая в $B_n^+$-матрице нулевой столбец, получаем $D_n^+$-матрицу. При
$k>0$ находим элемент $c_(u,k)$ произведения двух $D_n^+$-матриц по формуле
@eq:l2019-nonfinitary-b-positive и, кроме того,

$
  c_(u,-k)=sum_(j=k+1)^(u-1) lr((b_(j,-k)a_(u,j)-a_(j,-k)b_(u,j)))
  +sum_(j>0) lr((a_(k,j)b_(u,-j)-b_(k,j)a_(u,-j)))
  -sum_(j<0) lr((a_(u,-j)b_(k,j)-b_(u,-j)a_(k,j))).
$
<eq:l2019-nonfinitary-d-negative>

#lemma[
  Лиево произведение $alpha ast beta=gamma=norm(c_(i,j))$ любых двух
  $D_n$-матриц $alpha=norm(a_(i,j))$ и $beta=norm(b_(i,j))$ определяют формулы
  @eq:l2019-nonfinitary-b-positive и @eq:l2019-nonfinitary-d-negative.
] <lem:l2019-nonfinitary-d-formulas>

Далее выписываем произвольную $C_n^+$-матрицу $alpha=norm(a_(u,v))$:

$
  mat(
    delim: #none,
    , , a_(1,-1), , ;
    , a_(2,-2), a_(2,-1), a_(2,1), ;
    dots, dots, dots, dots, dots;
    a_(n,-n), dots a_(n,-2), a_(n,-1), a_(n,1) dots, a_(n,n-1);
  ).
$

С помощью формулы @eq:l2019-nonfinitary-expanded-bracket аналогично получаем:

$
  c_(u,k)=sum_(j=k)^(u-1) lr((a_(u,j)b_(j,k)-b_(u,j)a_(j,k))),
  quad k>=1;
$
<eq:l2019-nonfinitary-c-positive>

$
  c_(u,-k)=sum_(j=k)^(u-1) lr((b_(j,-k)a_(u,j)-a_(j,-k)b_(u,j)))
  +sum_(j>0) lr((a_(k,j)b_(u,-j)-b_(k,j)a_(u,-j)))
  +sum_(-k<j<0) lr((a_(u,-j)b_(k,j)-b_(u,-j)a_(k,j)));
$
<eq:l2019-nonfinitary-c-negative>

$
  #source(9, printed: 47)c_(u,-u)=2sum_(j=1)^(u-1)
  lr((a_(u,j)b_(u,-j)-b_(u,j)a_(u,-j))).
$
<eq:l2019-nonfinitary-c-long>

#lemma[
  Формулы @eq:l2019-nonfinitary-c-positive, @eq:l2019-nonfinitary-c-negative и
  @eq:l2019-nonfinitary-c-long определяют лиево произведение
  $alpha ast beta=gamma=norm(c_(i,j))$ любых двух $C_n$-матриц
  $alpha=norm(a_(i,j))$ и $beta=norm(b_(i,j))$.
] <lem:l2019-nonfinitary-c-formulas>

По аналогии с финитарным кольцом Ли $FNT(Gamma, K)$ с произвольной цепью $Gamma$
(тип $A_Gamma$), построим обобщенные финитарные кольца Ли $FNB_Gamma lr((K))$,
$FNC_Gamma lr((K))$ и $FND_Gamma lr((K))$. Напомним, что биективное соответствие
$prime:Gamma arrow Gamma'$ называют _изометрией_, если оно сохраняет отношение
порядка (т. е. из $i<=j$ следует $i'<=j'$), и называют _антиизометрией_, если
отношение порядка меняется на противоположное.

Зафиксируем цепь $Gamma$ с антиизометрией $prime$ такой, что $i'<=j$ для всех
$i,j in Gamma$, и положим $tilde(Gamma)=Gamma' union Gamma$. Тогда при
$Gamma' inter Gamma!=emptyset$ пересечение содержит единственный элемент.
Обозначим его через 0, а через $FNB_Gamma lr((K))$ — $K$-модуль с базисом

$ lr({e_(i,m) | i in Gamma,m in tilde(Gamma),i'<m<i}). $
<eq:l2019-nonfinitary-bd-basis>

При $Gamma' inter Gamma=emptyset$ через $FND_Gamma lr((K))$ обозначаем
$K$-модуль с такой же записью базиса, а $K$-модуль с базисом
$lr({e_(i,m) | i in Gamma,m in tilde(Gamma),i'<=m<i})$ — через
$FNC_Gamma lr((K))$.

Указанный выбор модулей реализуется, например, когда $Gamma$ выбирается как
подцепь цепи целых неотрицательных чисел с антиизометрией $i'=-i$.

Построенные $K$-модули превращаем в финитарные лиевы алгебры, определяя
произведения базисных элементов в них, с учетом леммы
@lem:l2019-nonfinitary-chevalley-signs, по правилу
[@bib:l2019-nonfinitary-Levchuk2009]:

$
  e_(i,j) ast e_(j,v)=e_(i,v); quad e_(i,j) ast e_(k,t)=0,
  quad j!=k,i!=t,t!=j';
$

$
  e_(i,0) ast e_(j,0)=2e_(i,j') quad (G=B_Gamma);
  quad e_(i,j) ast e_(i,j')=2e_(i,i') quad (G=C_Gamma), quad i>j in Gamma;
$

$
  e_(i,m) ast e_(j,m')=e_(i,j'), quad j'<m<j<i,j!=0,
  quad e_(i,m) ast e_(i,m')=0 quad (G=B_Gamma,D_Gamma);
$

$
  e_(j,k) ast e_(i,k')=e_(i,k) ast e_(j,k')=e_(i,j'),
  quad i>j>k in Gamma quad (G=C_Gamma).
$

Сейчас замечаем, что полученные в леммах @lem:l2019-nonfinitary-b-formulas,
@lem:l2019-nonfinitary-d-formulas и @lem:l2019-nonfinitary-c-formulas формулы
умножения $Phi^+$-матриц корректно обобщаются на $G$-матрицы
$alpha=norm(a_(i,m))$ типа $G=B_Gamma,C_Gamma$ и $D_Gamma$. Таким образом,
приходим к финитарным кольцам Ли $FNB_Gamma lr((K))$, $FNC_Gamma lr((K))$ и
$FND_Gamma lr((K))$.

#theorem[
  Формулы умножения обобщенных матриц в кольцах Ли $FNB_Gamma lr((K))$,
  $FND_Gamma lr((K))$ и $FNC_Gamma lr((K))$ определяются для произвольной цепи
  $Gamma$ корректно формулами из лемм @lem:l2019-nonfinitary-b-formulas,
  @lem:l2019-nonfinitary-d-formulas и @lem:l2019-nonfinitary-c-formulas
  соответственно.
] <th:l2019-nonfinitary-finitary-products>

#source(10, printed: 48)Финитарные обобщения унипотентных подгрупп групп Шевалле
классических типов (по аналогии с обобщениями унитреугольных групп)
представляются в [@bib:l2019-nonfinitary-Levchuk2009] как присоединенные группы
финитарных алгебр $FNG(K)$ типа $G=B_Gamma,D_Gamma$ и $C_Gamma$. Там же выписаны
основные соотношения в терминах элементарных элементов и найдены автоморфизмы.
