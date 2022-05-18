import java.util.stream.LongStream;

public class SieveOfEratosthenes {
    static LongBitSet primeCandidates;
    /**
     * returns a boolean array for prime numbers
     * @param max the maximum value to search for primes
     * @return boolean array of integers with primes true
     */
    public static boolean[] sieveOfEratosthenes(int max){

        boolean[] primeCandidates = new boolean[max]; //defaults to false
        for(int i=2; i<max; i++ )
            primeCandidates[i]=true;

        for(int i=2; i<Math.sqrt(max);i++){
            if(primeCandidates[i] == true){
                //all multiples of i*i, except i, are not primeCandidates
                for(int j = i + i; j<max; j=j+i)
                    primeCandidates[j]=false;
            }
        }
        return primeCandidates;
    }

    public static LongBitSet sieveOfEratosthenes(long max){

        primeCandidates = new LongBitSet(max); //defaults to false
        primeCandidates.set(2L, max);

        for(long i=2; i<Math.sqrt(max);i++){
            if(primeCandidates.get(i)) {
                // all multiples of i*i, except i, are not primeCandidates
                for(long j = i + i; j<max; j=j+i)
                    primeCandidates.clear(j);
            }
        }
        return primeCandidates;
    }

    public static LongBitSet neatSieveOfEratosthenes(long max){
        primeCandidates = new LongBitSet(max);
        primeCandidates.set(2L, max);

        final long maxSqrt = (long) Math.sqrt(max);
        LongStream.iterate(2, l -> l++)
                .limit(maxSqrt)
                .filter(primeCandidates::get)
                .forEach(l -> clearMultiples(l, maxSqrt));
        return primeCandidates;
    }

    private static void clearMultiples(long i, long max) {
        for(long j = i + i; j < max; j=j+i)
            primeCandidates.clear(j);
    }

    /**
     * print the index number for all true in given array
     * @param a boolean array
     */
    public static void printTrue(boolean[] arr){
        for(int i=0; i<arr.length; i++){
            if(arr[i]==true){
                System.out.print(i + ", ");
            }
        }
    }

    public static long cardinality() {
        return primeCandidates.cardinality();
    }
}
