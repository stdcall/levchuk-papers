#import "defs.typ": *
#heading(level: 3)[Изоморфизмы и элементарная эквивалентность ассоциированных
  колец] <sec:l2012-model-associated>
С каждым ассоциативным кольцом $R$ ассоциируют кольцо Ли $Lambda(R):=(R,+,ast)$
с лиевым умножением $alpha ast beta=alpha beta-beta
alpha$; замена $alpha beta$ на $alpha beta+beta alpha$ дает кольцо Йордана
$J(R)$. Если $R$ — радикальное кольцо, то $x arrow.r 1+x$ $(x in R)$ —
изоморфизм его присоединенной группы $G(R)$ и для групп автоморфизмов легко
получаем равенства
$ Aut R=Aut G(R) inter Aut J(R)=Aut G(R) inter Aut Lambda(R). $
При $R=NT(n, K)$ получаем изоморфизм групп $G(R) tilde.eq UT(n, K)$. Их
автоморфизмы и — когда либо $n>3$, либо $n=3$ и
#source(77, printed: 77)
кольцо $K$ коммутативное или без делителей нуля — также $Aut Lambda(R)$ описаны
в [@bib:l2012-model-Levchuk1975,
теорема~@th:l1975-automorphisms-ring-decomposition] и
[@bib:l2012-model-Levchuk1983, теоремы @th:l1983-main-automorphisms и
@th:l1983-rank-four]; описание $Aut J(R)$, см.
[@bib:l2012-model-LevchukMinakova2009; @bib:l2012-model-LevchukMinakova2010].

Схема [@bib:l2012-model-Levchuk1983] переносится в
[@bib:l2012-model-KuzucuogluLevchuk2004; @th:l2004-finitary-main[основная
  теорема]] для описания изоморфизмов, в том числе и в случаях некоммутативных
колец коэффициентов. Нам потребуется обобщение.

Пусть $K$ и $S$ — ассоциативные кольца с единицами $1_K$ и $1_S$ и пусть $f$ —
центральный идемпотент кольца $K$. Левое и правое пирсовы разложения кольца $K$
по $f$ совпадают. Изоморфизм $theta:K^+ arrow.r S^+$ аддитивных групп с условием
$theta(1_K)=1_S$ называется _$f$-изоморфизмом_ или _идемпотентным изоморфизмом_
(ассоциативных) колец $K$ и $S$, если он индуцирует изоморфизм идеала $f K$ и
анти-изоморфизм идеала $(1_K-f)K$.

Кольца $K$ и $S$ назовем _идемпотентно изоморфными_, если существует
идемпотентный изоморфизм между ними. Положим $R=NT(n, K)$ и $R'=NT(m, S)$.
Справедлива #theorem[
  Пусть либо $n>4$, либо кольцо $K$ коммутативное и $n=3$ или 4. Тогда любая из
  изоморфностей
  $
    UT(n, K) tilde.eq UT(m, S), quad Lambda(R) tilde.eq Lambda(R'), quad
    J(R) tilde.eq J(R')
  $
  равносильна тому, что $m=n$ и кольца $K$ и $S$ идемпотентно изоморфны.
] <th:l2012-model-idempotent-isomorphisms>
Доказательство в случаях $UT(n, K) tilde.eq UT(m, S)$ и
$Lambda(R) tilde.eq Lambda(R')$ приведено в
[@bib:l2012-model-KuzucuogluLevchuk2004; теорема
@th:l2004-finitary-finite-chain-isomorphisms при $n>4$], а в случае
$J(R) tilde.eq J(R')$ модифицируется из доказательства теоремы 2.1 из
[@bib:l2012-model-LevchukMinakova2010] (см.
@th:l2008-model-elementary-equivalence).

Связь элементарной эквивалентности ассоциированных колец, а также присоединенных
групп с элементарными свойствами основных колец выявляет (см.
[@bib:l2012-model-LevchukMinakova2009; @bib:l2012-model-LevchukMinakova2010])
#theorem[
  В условиях теоремы @th:l2012-model-idempotent-isomorphisms хотя бы одна из
  элементарных эквивалентностей
  $
    UT(n, K) equiv UT(n, S), quad Lambda(R) equiv Lambda(R'), quad
    J(R) equiv J(R')
  $
  выполняется тогда и только тогда, когда существуют центральные идемпотенты $f$
  в $K$ и $g$ в $S$ такие, что $f K equiv g S$ и $(1-f)K equiv [(1-g)S]^"op"$.
] <th:l2012-model-idempotent-equivalence>
#remark[
  Описание изоморфизмов $Lambda(R) arrow.l.r Lambda(R')$ и
  $UT(n, K) arrow.l.r UT(m, S)$ при $n=m=4$ известно
  [@bib:l2012-model-Levchuk1983; @bib:l2012-model-KuzucuogluLevchuk2004;
  замечание @rem:l2004-finitary-small-ranks]. Неизвестно однако, останется ли
  теорема @th:l2012-model-idempotent-isomorphisms справедливой для $n=4$, если
  #source(78, printed: 78)
  снять ограничение на $K$? Как показала Е. В. Минакова
  [@bib:l2012-model-Minakova2008], теорема @th:l2012-model-niltriangular-rings
  Видэла остается справедливой, если требовать в ней ассоциативность одного из
  колец коэффициентов. Аналогичные вопросы при $n=3$ естественны и для
  изоморфностей из теоремы @th:l2012-model-idempotent-isomorphisms;
  ассоциативность колец коэффициентов в определении унитреугольной группы
  $UT(n, K) tilde.eq G(R)$ и колец $Lambda(R)$ и $J(R)$ требуется лишь для
  степеней $n>3$. Остается открытым вопрос О. В. Белеградека
  [@bib:l2012-model-Belegradek1999]:
] <rem:l2012-model-rank-four>
#question[
  Существует ли изоморфизм $UT(3, K) tilde.eq UT(3, S)$ для ассоциативного и
  неассоциативного колец коэффициентов?
] <pr:l2012-model-nonassociative>
