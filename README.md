# LongBitSet
java.util.BitSet modifications to make it reach max index bit. By having int based interface BitSet can't reach `Ingeter.MAX_VALUE &lt;&lt; 6` bits.

This class is used to try to maximize the number of prime numbers mapped by `CoprimeHarmonicsLongBitSet.java` were a new prime numbers sieve is implemented per article
[The dynamic of prime numbers](https://mirror.xyz/0x62514E8C74B1B188dFCD76D2171c96EF1845Ba02/PhwGsMoDsGGfbagtxAhjM5OyvIPnFfF6dhBYb4QICfQ) of my authorship.
