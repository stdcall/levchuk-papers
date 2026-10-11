#import "@preview/cetz:0.5.2": canvas, draw
#import "../../main-defs.typ": GF
#let DF = math.upright("DF")

#let lattice = canvas(length: 8mm, {
  import draw: *
  let layers = ((1,), (3, 5, 2), (6, 15, 10, 4), (12, 30, 20), (60,))
  let positions = (:)
  for (rank, layer) in layers.enumerate() {
    for (i, h) in layer.enumerate() {
      positions.insert(str(h), (3.1 * (i - (layer.len() - 1) / 2), 1.8 * rank))
    }
  }
  let divisors = layers.flatten()
  for h in divisors {
    for k in divisors.filter(k => k > h and calc.rem(k, h) == 0) {
      let between = divisors.any(d => (
        d > h and d < k and calc.rem(d, h) == 0 and calc.rem(k, d) == 0
      ))
      if not between {
        line(positions.at(str(h)), positions.at(str(k)), stroke: 0.7pt)
      }
    }
  }
  for h in divisors {
    let pos = positions.at(str(h))
    let power = 1
    for _ in range(h) { power = calc.rem(2 * power, 15) }
    let ratio = 0
    for _ in range(calc.quo(60, h)) {
      ratio = calc.rem(power * ratio + 1, 15)
    }
    // gcd(4j,h), with j the sub-near-field congruence modulo 15.
    let a = 4 * calc.rem(ratio, 15)
    let b = h
    while b != 0 {
      let r = calc.rem(a, b)
      a = b
      b = r
    }
    let field = a == h
    circle(pos, radius: 0.42, fill: if field { luma(85%) } else { white })
    content(pos, $2^#h$)
    let description = if field { $GF(2^#h)$ } else {
      $DF(2^#a, #calc.quo(h, a))$
    }
    let annotation = stack(
      dir: ttb,
      spacing: 2pt,
      text(size: 9pt, description),
      ..if h == 4 { (text(size: 8pt)[Центр],) } else { () },
    )
    content(
      (pos.at(0), pos.at(1) - 0.64),
      box(fill: white, inset: 1pt, annotation),
      anchor: "north",
    )
  }
})
#figure(
  lattice,
  caption: [Решетка под-почти-полей в почти-поле Диксона порядка $2^60$],
  numbering: none,
) <fig:l2019-nearfields-lattice>
