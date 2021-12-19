/*
 * Copyright (c) 1995, 2014, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 */

import java.io.*;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.LongBuffer;
import java.util.Arrays;
import java.util.NoSuchElementException;
import java.util.PrimitiveIterator;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.LongStream;
import java.util.stream.StreamSupport;

/**
 * This class implements a vector of bits that grows as needed. Each
 * component of the bit set has a {@code boolean} value. The
 * bits of a {@code LongBitSet} are indexed by nonnegative integers.
 * Individual indexed bits can be examined, set, or cleared. One
 * {@code LongBitSet} may be used to modify the contents of another
 * {@code LongBitSet} through logical AND, logical inclusive OR, and
 * logical exclusive OR operations.
 *
 * <p>By default, all bits in the set initially have the value
 * {@code false}.
 *
 * <p>Every bit set has a current size, which is the number of bits
 * of space currently in use by the bit set. Note that the size is
 * related to the implementation of a bit set, so it may change with
 * implementation. The length of a bit set relates to logical length
 * of a bit set and is defined independently of implementation.
 *
 * <p>Unless otherwise noted, passing a null parameter to any of the
 * methods in a {@code LongBitSet} will result in a
 * {@code NullPointerException}.
 *
 * <p>A {@code LongBitSet} is not safe for multithreaded use without
 * external synchronization.
 *
 * @author  Arthur van Hoff
 * @author  Michael McCloskey
 * @author  Martin Buchholz
 * @since   JDK1.0
 */
public class LongBitSet implements Cloneable, java.io.Serializable {
    /*
     * LongBitSets are packed into arrays of "words."  Currently a word is
     * a long, which consists of 64 bits, requiring 6 address bits.
     * The choice of word size is determined purely by performance concerns.
     */
    private final static int ADDRESS_BITS_PER_WORD = 6;
    private final static int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;
    private final static int BIT_INDEX_MASK = BITS_PER_WORD - 1;

    /* Used to shift left or right for a partial word mask */
    private static final long WORD_MASK = 0xffffffffffffffffL;

    /**
     * @serialField bits long[]
     *
     * The bits in this LongBitSet.  The ith bit is stored in bits[i/64] at
     * bit position i % 64 (where bit position 0 refers to the least
     * significant bit and 63 refers to the most significant bit).
     */
    private static final ObjectStreamField[] serialPersistentFields = {
            new ObjectStreamField("bits", long[].class),
    };

    /**
     * The internal field corresponding to the serialField "bits".
     */
    private long[] words;

    /**
     * The number of words in the logical size of this LongBitSet.
     */
    private transient int wordsInUse = 0;

    /**
     * Whether the size of "words" is user-specified.  If so, we assume
     * the user knows what he's doing and try harder to preserve it.
     */
    // TODO: check if transient is useful on sizeIsSticky == true.
    private boolean sizeIsSticky = false;

    /**
     * Holds user provided nbits on constructor.
     */
    private long stickyLength = -1;

    /**
     * If sizeIsSticky is true, check invariants only once.
     */
    private boolean invariantsMet = false;

    /* use serialVersionUID from JDK 1.0.2 for interoperability */
    private static final long serialVersionUID = 7997698588986878753L;

    /**
     * Given a bit index, return word index containing it.
     */
    private static int wordIndex(long bitIndex) {
        // TODO: Check that (int) here won't lose precision.
        long wordIndex = bitIndex >> ADDRESS_BITS_PER_WORD;
        if (wordIndex > Integer.MAX_VALUE) {
            throw new IndexOutOfBoundsException("Can't map bits to a bytes array, bit set too long: " + bitIndex);
        }
        return (int) wordIndex;
    }

    /**
     * Every public method must preserve these invariants.
     */
    private void checkInvariants() {
        if (sizeIsSticky && invariantsMet)
            return;

        assert(wordsInUse == 0 || words[wordsInUse - 1] != 0);
        assert(wordsInUse >= 0 && wordsInUse <= words.length);
        assert(wordsInUse == words.length || words[wordsInUse] == 0);
        invariantsMet = sizeIsSticky;
    }

    /**
     * Sets the field wordsInUse to the logical size in words of the bit set.
     * WARNING:This method assumes that the number of words actually in use is
     * less than or equal to the current value of wordsInUse!
     *
     * Note: Only if user didn't set a fixed size.
     */
    private void recalculateWordsInUse() {
        if (sizeIsSticky)
            return;

        // Traverse the LongBitSet until a used word is found
        int i;
        for (i = wordsInUse-1; i >= 0; i--)
            if (words[i] != 0)
                break;

        wordsInUse = i+1; // The new logical size
    }

    /**
     * Creates a new bit set. All bits are initially {@code false}.
     */
    public LongBitSet() {
        initWords(BITS_PER_WORD);
        sizeIsSticky = false;
    }

    /**
     * Creates a bit set whose initial size is large enough to explicitly
     * represent bits with indices in the range {@code 0} through
     * {@code nbits-1}. All bits are initially {@code false}.
     *
     * @param  nbits the initial size of the bit set
     * @throws NegativeArraySizeException if the specified initial size
     *         is negative
     */
    public LongBitSet(long nbits) {
        // nbits can't be negative; size 0 is OK
        if (nbits < 0)
            throw new NegativeArraySizeException("nbits < 0: " + nbits);

        initWords(nbits);
        stickyLength = nbits;
        sizeIsSticky = true;
    }

    private void initWords(long nbits) {
        words = new long[wordIndex(nbits-1) + 1];
    }

    /**
     * Creates a bit set using words as the internal representation.
     * The last word (if there is one) must be non-zero.
     */
    private LongBitSet(long[] words) {
        this.words = words;
        this.wordsInUse = words.length;
        checkInvariants();
    }

    /**
     * Returns a new bit set containing all the bits in the given long array.
     *
     * <p>More precisely,
     * <br>{@code LongBitSet.valueOf(longs).get(n) == ((longs[n/64] & (1L<<(n%64))) != 0)}
     * <br>for all {@code n < 64 * longs.length}.
     *
     * <p>This method is equivalent to
     * {@code LongBitSet.valueOf(LongBuffer.wrap(longs))}.
     *
     * @param longs a long array containing a little-endian representation
     *        of a sequence of bits to be used as the initial bits of the
     *        new bit set
     * @return a {@code LongBitSet} containing all the bits in the long array
     * @since 1.7
     */
    public static LongBitSet valueOf(long[] longs) {
        int n;
        for (n = longs.length; n > 0 && longs[n - 1] == 0; n--)
            ;
        return new LongBitSet(Arrays.copyOf(longs, n));
    }

    /**
     * Returns a new bit set containing all the bits in the given long
     * buffer between its position and limit.
     *
     * <p>More precisely,
     * <br>{@code LongBitSet.valueOf(lb).get(n) == ((lb.get(lb.position()+n/64) & (1L<<(n%64))) != 0)}
     * <br>for all {@code n < 64 * lb.remaining()}.
     *
     * <p>The long buffer is not modified by this method, and no
     * reference to the buffer is retained by the bit set.
     *
     * @param lb a long buffer containing a little-endian representation
     *        of a sequence of bits between its position and limit, to be
     *        used as the initial bits of the new bit set
     * @return a {@code LongBitSet} containing all the bits in the buffer in the
     *         specified range
     * @since 1.7
     */
    public static LongBitSet valueOf(LongBuffer lb) {
        lb = lb.slice();
        int n;
        for (n = lb.remaining(); n > 0 && lb.get(n - 1) == 0; n--)
            ;
        long[] words = new long[n];
        lb.get(words);
        return new LongBitSet(words);
    }

    /**
     * Returns a new bit set containing all the bits in the given byte array.
     *
     * <p>More precisely,
     * <br>{@code LongBitSet.valueOf(bytes).get(n) == ((bytes[n/8] & (1<<(n%8))) != 0)}
     * <br>for all {@code n <  8 * bytes.length}.
     *
     * <p>This method is equivalent to
     * {@code LongBitSet.valueOf(ByteBuffer.wrap(bytes))}.
     *
     * @param bytes a byte array containing a little-endian
     *        representation of a sequence of bits to be used as the
     *        initial bits of the new bit set
     * @return a {@code LongBitSet} containing all the bits in the byte array
     * @since 1.7
     */
    public static LongBitSet valueOf(byte[] bytes) {
        return LongBitSet.valueOf(ByteBuffer.wrap(bytes));
    }

    /**
     * Returns a new bit set containing all the bits in the given byte
     * buffer between its position and limit.
     *
     * <p>More precisely,
     * <br>{@code LongBitSet.valueOf(bb).get(n) == ((bb.get(bb.position()+n/8) & (1<<(n%8))) != 0)}
     * <br>for all {@code n < 8 * bb.remaining()}.
     *
     * <p>The byte buffer is not modified by this method, and no
     * reference to the buffer is retained by the bit set.
     *
     * @param bb a byte buffer containing a little-endian representation
     *        of a sequence of bits between its position and limit, to be
     *        used as the initial bits of the new bit set
     * @return a {@code LongBitSet} containing all the bits in the buffer in the
     *         specified range
     * @since 1.7
     */
    public static LongBitSet valueOf(ByteBuffer bb) {
        bb = bb.slice().order(ByteOrder.LITTLE_ENDIAN);
        int n;
        for (n = bb.remaining(); n > 0 && bb.get(n - 1) == 0; n--)
            ;
        long[] words = new long[(n + 7) / 8];
        bb.limit(n);
        int i = 0;
        while (bb.remaining() >= 8)
            words[i++] = bb.getLong();
        for (int remaining = bb.remaining(), j = 0; j < remaining; j++)
            words[i] |= (bb.get() & 0xffL) << (8 * j);
        return new LongBitSet(words);
    }

    /**
     * Returns a new byte array containing all the bits in this bit set.
     *
     * <p>More precisely, if
     * <br>{@code byte[] bytes = s.toByteArray();}
     * <br>then {@code bytes.length == (s.length()+7)/8} and
     * <br>{@code s.get(n) == ((bytes[n/8] & (1<<(n%8))) != 0)}
     * <br>for all {@code n < 8 * bytes.length}.
     *
     * @return a byte array containing a little-endian representation
     *         of all the bits in this bit set
     * @since 1.7
     */
    public byte[] toByteArray() {
        long bitsInUse = (long) wordsInUse * (long) BITS_PER_WORD;
        if (bitsInUse > Integer.MAX_VALUE) {
            throw new IndexOutOfBoundsException("Can't map bits to a bytes array, bit set too long: " + bitsInUse);
        }
        int n = wordsInUse;
        if (n == 0)
            return new byte[0];
        int len = 8 * (n-1);
        for (long x = words[n - 1]; x != 0; x >>>= 8)
            len++;
        byte[] bytes = new byte[len];
        ByteBuffer bb = ByteBuffer.wrap(bytes).order(ByteOrder.LITTLE_ENDIAN);
        for (int i = 0; i < n - 1; i++)
            bb.putLong(words[i]);
        for (long x = words[n - 1]; x != 0; x >>>= 8)
            bb.put((byte) (x & 0xff));
        return bytes;
    }

    /**
     * Returns a new long array containing all the bits in this bit set.
     *
     * <p>More precisely, if
     * <br>{@code long[] longs = s.toLongArray();}
     * <br>then {@code longs.length == (s.length()+63)/64} and
     * <br>{@code s.get(n) == ((longs[n/64] & (1L<<(n%64))) != 0)}
     * <br>for all {@code n < 64 * longs.length}.
     *
     * @return a long array containing a little-endian representation
     *         of all the bits in this bit set
     * @since 1.7
     */
    public long[] toLongArray() {
        return Arrays.copyOf(words, wordsInUse);
    }

    /**
     * Ensures that the LongBitSet can hold enough words.
     * @param wordsRequired the minimum acceptable number of words.
     */
    private void ensureCapacity(int wordsRequired) {
        if (words.length < wordsRequired) {
            // Allocate larger of doubled size or required size
            int request = Math.max(
                    (int) Math.min(2L * (long) words.length, Integer.MAX_VALUE),
                    wordsRequired);
            words = Arrays.copyOf(words, request);
            sizeIsSticky = false;
        }
    }

    /**
     * Ensures that the LongBitSet can accommodate a given wordIndex,
     * temporarily violating the invariants.  The caller must
     * restore the invariants before returning to the user,
     * possibly using recalculateWordsInUse().
     * @param wordIndex the index to be accommodated.
     */
    private void expandTo(int wordIndex) {
        int wordsRequired = wordIndex+1;
        if (wordsInUse < wordsRequired) {
            ensureCapacity(wordsRequired);
            wordsInUse = wordsRequired;
        }
    }

    /**
     * Checks that fromIndex ... toIndex is a valid range of bit indices.
     */
    private static void checkRange(long fromIndex, long toIndex) {
        if (fromIndex < 0)
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        if (toIndex < 0)
            throw new IndexOutOfBoundsException("toIndex < 0: " + toIndex);
        if (fromIndex > toIndex)
            throw new IndexOutOfBoundsException("fromIndex: " + fromIndex +
                    " > toIndex: " + toIndex);
    }

    /**
     * Sets the bit at the specified index to the complement of its
     * current value.
     *
     * @param  bitIndex the index of the bit to flip
     * @throws IndexOutOfBoundsException if the specified index is negative
     * @since  1.4
     */
    public void flip(long bitIndex) {
        if (bitIndex < 0)
            throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);

        int wordIndex = wordIndex(bitIndex);
        expandTo(wordIndex);

        words[wordIndex] ^= (1L << bitIndex);

        // TODO: this call looks redundant. Unless it's to shorten logical size, which should be optional.
        recalculateWordsInUse();
        checkInvariants();
    }

    /**
     * Sets each bit from the specified {@code fromIndex} (inclusive) to the
     * specified {@code toIndex} (exclusive) to the complement of its current
     * value.
     *
     * @param  fromIndex index of the first bit to flip
     * @param  toIndex index after the last bit to flip
     * @throws IndexOutOfBoundsException if {@code fromIndex} is negative,
     *         or {@code toIndex} is negative, or {@code fromIndex} is
     *         larger than {@code toIndex}
     * @since  1.4
     */
    public void flip(long fromIndex, long toIndex) {
        checkRange(fromIndex, toIndex);

        if (fromIndex == toIndex)
            return;

        int startWordIndex = wordIndex(fromIndex);
        int endWordIndex   = wordIndex(toIndex - 1);
        expandTo(endWordIndex);

        long firstWordMask = WORD_MASK << fromIndex;
        long lastWordMask  = WORD_MASK >>> -toIndex;
        if (startWordIndex == endWordIndex) {
            // Case 1: One word
            words[startWordIndex] ^= (firstWordMask & lastWordMask);
        } else {
            // Case 2: Multiple words
            // Handle first word
            words[startWordIndex] ^= firstWordMask;

            // Handle intermediate words, if any
            for (int i = startWordIndex+1; i < endWordIndex; i++)
                words[i] ^= WORD_MASK;

            // Handle last word
            words[endWordIndex] ^= lastWordMask;
        }

        recalculateWordsInUse();
        checkInvariants();
    }

    /**
     * Sets the bit at the specified index to {@code true}.
     *
     * @param  bitIndex a bit index
     * @throws IndexOutOfBoundsException if the specified index is negative
     * @since  JDK1.0
     */
    public void set(long bitIndex) {
        if (bitIndex < 0)
            throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);

        int wordIndex = wordIndex(bitIndex);
        expandTo(wordIndex);

        words[wordIndex] |= (1L << bitIndex); // Restores invariants

        checkInvariants();
    }

    /**
     * Sets the bit at the specified index to the specified value.
     *
     * @param  bitIndex a bit index
     * @param  value a boolean value to set
     * @throws IndexOutOfBoundsException if the specified index is negative
     * @since  1.4
     */
    public void set(long bitIndex, boolean value) {
        // TODO: compare performance with ? : ;
        if (value)
            set(bitIndex);
        else
            clear(bitIndex);
    }

    /**
     * Sets the bits from the specified {@code fromIndex} (inclusive) to the
     * specified {@code toIndex} (exclusive) to {@code true}.
     *
     * @param  fromIndex index of the first bit to be set
     * @param  toIndex index after the last bit to be set
     * @throws IndexOutOfBoundsException if {@code fromIndex} is negative,
     *         or {@code toIndex} is negative, or {@code fromIndex} is
     *         larger than {@code toIndex}
     * @since  1.4
     */
    public void set(long fromIndex, long toIndex) {
        checkRange(fromIndex, toIndex);

        if (fromIndex == toIndex)
            return;

        // Increase capacity if necessary
        int startWordIndex = wordIndex(fromIndex);
        int endWordIndex   = wordIndex(toIndex - 1);
        expandTo(endWordIndex);

        long firstWordMask = WORD_MASK << fromIndex;
        long lastWordMask  = WORD_MASK >>> -toIndex;
        if (startWordIndex == endWordIndex) {
            // Case 1: One word
            words[startWordIndex] |= (firstWordMask & lastWordMask);
        } else {
            // Case 2: Multiple words
            // Handle first word
            words[startWordIndex] |= firstWordMask;

            // Handle intermediate words, if any
            for (int i = startWordIndex+1; i < endWordIndex; i++)
                words[i] = WORD_MASK;

            // Handle last word (restores invariants)
            words[endWordIndex] |= lastWordMask;
        }

        checkInvariants();
    }

    /**
     * Sets the bits from the specified {@code fromIndex} (inclusive) to the
     * specified {@code toIndex} (exclusive) to the specified value.
     *
     * @param  fromIndex index of the first bit to be set
     * @param  toIndex index after the last bit to be set
     * @param  value value to set the selected bits to
     * @throws IndexOutOfBoundsException if {@code fromIndex} is negative,
     *         or {@code toIndex} is negative, or {@code fromIndex} is
     *         larger than {@code toIndex}
     * @since  1.4
     */
    public void set(long fromIndex, long toIndex, boolean value) {
        if (value)
            set(fromIndex, toIndex);
        else
            clear(fromIndex, toIndex);
    }

    /**
     * Sets the bit specified by the index to {@code false}.
     *
     * @param  bitIndex the index of the bit to be cleared
     * @throws IndexOutOfBoundsException if the specified index is negative
     * @since  JDK1.0
     */
    public void clear(long bitIndex) {
        if (bitIndex < 0)
            throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);

        int wordIndex = wordIndex(bitIndex);
        if (wordIndex >= wordsInUse)
            return;

        words[wordIndex] &= ~(1L << bitIndex);

        recalculateWordsInUse();
        checkInvariants();
    }

    /**
     * Sets the bits from the specified {@code fromIndex} (inclusive) to the
     * specified {@code toIndex} (exclusive) to {@code false}.
     *
     * @param  fromIndex index of the first bit to be cleared
     * @param  toIndex index after the last bit to be cleared
     * @throws IndexOutOfBoundsException if {@code fromIndex} is negative,
     *         or {@code toIndex} is negative, or {@code fromIndex} is
     *         larger than {@code toIndex}
     * @since  1.4
     */
    public void clear(long fromIndex, long toIndex) {
        checkRange(fromIndex, toIndex);

        if (fromIndex == toIndex)
            return;

        int startWordIndex = wordIndex(fromIndex);
        if (startWordIndex >= wordsInUse)
            return;

        int endWordIndex = wordIndex(toIndex - 1);
        if (endWordIndex >= wordsInUse) {
            toIndex = length();
            endWordIndex = wordsInUse - 1;
        }

        long firstWordMask = WORD_MASK << fromIndex;
        long lastWordMask  = WORD_MASK >>> -toIndex;
        if (startWordIndex == endWordIndex) {
            // Case 1: One word
            words[startWordIndex] &= ~(firstWordMask & lastWordMask);
        } else {
            // Case 2: Multiple words
            // Handle first word
            words[startWordIndex] &= ~firstWordMask;

            // Handle intermediate words, if any
            for (int i = startWordIndex+1; i < endWordIndex; i++)
                words[i] = 0;

            // Handle last word
            words[endWordIndex] &= ~lastWordMask;
        }

        recalculateWordsInUse();
        checkInvariants();
    }

    /**
     * Sets all of the bits in this LongBitSet to {@code false}.
     *
     * @since 1.4
     */
    public void clear() {
        // TODO: Now that sizeIsSticky prevents recalculating wordsInUse compare performance of this vs
        //   sizeIsSticky = false and recalculateWordsInUse() before setting the whole array.
//        if (sizeIsSticky) {
//            sizeIsSticky = false;
//            recalculateWordsInUse();
//            sizeIsSticky = true;
//        }
        while (wordsInUse > 0)
            words[--wordsInUse] = 0;
    }

    /**
     * Returns the value of the bit with the specified index. The value
     * is {@code true} if the bit with the index {@code bitIndex}
     * is currently set in this {@code LongBitSet}; otherwise, the result
     * is {@code false}.
     *
     * @param  bitIndex   the bit index
     * @return the value of the bit with the specified index
     * @throws IndexOutOfBoundsException if the specified index is negative
     */
    public boolean get(long bitIndex) {
        if (bitIndex < 0)
            throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);

        checkInvariants();

        int wordIndex = wordIndex(bitIndex);
        return (wordIndex < wordsInUse)
                && ((words[wordIndex] & (1L << bitIndex)) != 0);
    }

    /**
     * Returns a new {@code LongBitSet} composed of bits from this {@code LongBitSet}
     * from {@code fromIndex} (inclusive) to {@code toIndex} (exclusive).
     *
     * @param  fromIndex index of the first bit to include
     * @param  toIndex index after the last bit to include
     * @return a new {@code LongBitSet} from a range of this {@code LongBitSet}
     * @throws IndexOutOfBoundsException if {@code fromIndex} is negative,
     *         or {@code toIndex} is negative, or {@code fromIndex} is
     *         larger than {@code toIndex}
     * @since  1.4
     */
    public LongBitSet get(long fromIndex, long toIndex) {
        checkRange(fromIndex, toIndex);

        checkInvariants();

        long len = length();

        // If no set bits in range return empty LongBitSet
        if (len <= fromIndex || fromIndex == toIndex)
            return new LongBitSet(0);

        // An optimization
        if (toIndex > len)
            toIndex = len;

        LongBitSet result = new LongBitSet(toIndex - fromIndex);
        int targetWords = wordIndex(toIndex - fromIndex - 1) + 1;
        int sourceIndex = wordIndex(fromIndex);
        boolean wordAligned = ((fromIndex & BIT_INDEX_MASK) == 0);

        // Process all words but the last word
        for (int i = 0; i < targetWords - 1; i++, sourceIndex++)
            result.words[i] = wordAligned ? words[sourceIndex] :
                    (words[sourceIndex] >>> fromIndex) |
                            (words[sourceIndex+1] << -fromIndex);

        // Process the last word
        long lastWordMask = WORD_MASK >>> -toIndex;
        result.words[targetWords - 1] =
                ((toIndex-1) & BIT_INDEX_MASK) < (fromIndex & BIT_INDEX_MASK)
                        ? /* straddles source words */
                        ((words[sourceIndex] >>> fromIndex) |
                                (words[sourceIndex+1] & lastWordMask) << -fromIndex)
                        :
                        ((words[sourceIndex] & lastWordMask) >>> fromIndex);

        // Set wordsInUse correctly
        result.wordsInUse = targetWords;
        result.recalculateWordsInUse();
        result.checkInvariants();

        return result;
    }

    /**
     * Returns the index of the first bit that is set to {@code true}
     * that occurs on or after the specified starting index. If no such
     * bit exists then {@code -1} is returned.
     *
     * <p>To iterate over the {@code true} bits in a {@code LongBitSet},
     * use the following loop:
     *
     *  <pre> {@code
     * for (int i = bs.nextSetBit(0); i >= 0; i = bs.nextSetBit(i+1)) {
     *     // operate on index i here
     *     if (i == Integer.MAX_VALUE) {
     *         break; // or (i+1) would overflow
     *     }
     * }}</pre>
     *
     * @param  fromIndex the index to start checking from (inclusive)
     * @return the index of the next set bit, or {@code -1} if there
     *         is no such bit
     * @throws IndexOutOfBoundsException if the specified index is negative
     * @since  1.4
     */
    public long nextSetBit(long fromIndex) {
        if (fromIndex < 0)
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);

        checkInvariants();

        int u = wordIndex(fromIndex);
        if (u >= wordsInUse)
            return -1;

        long word = words[u] & (WORD_MASK << fromIndex);

        while (true) {
            if (word != 0)
                return (u * BITS_PER_WORD) + Long.numberOfTrailingZeros(word);
            if (++u == wordsInUse)
                return -1;
            word = words[u];
        }
    }

    /**
     * Returns the index of the first bit that is set to {@code false}
     * that occurs on or after the specified starting index.
     *
     * @param  fromIndex the index to start checking from (inclusive)
     * @return the index of the next clear bit
     * @throws IndexOutOfBoundsException if the specified index is negative
     * @since  1.4
     */
    public long nextClearBit(long fromIndex) {
        // Neither spec nor implementation handle LongBitSets of maximal length.
        // See 4816253.
        if (fromIndex < 0)
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);

        checkInvariants();

        int u = wordIndex(fromIndex);
        if (u >= wordsInUse)
            return fromIndex;

        long word = ~words[u] & (WORD_MASK << fromIndex);

        while (true) {
            if (word != 0)
                return (u * BITS_PER_WORD) + Long.numberOfTrailingZeros(word);
            if (++u == wordsInUse)
                return wordsInUse * BITS_PER_WORD;
            word = ~words[u];
        }
    }

    /**
     * Returns the index of the nearest bit that is set to {@code true}
     * that occurs on or before the specified starting index.
     * If no such bit exists, or if {@code -1} is given as the
     * starting index, then {@code -1} is returned.
     *
     * <p>To iterate over the {@code true} bits in a {@code LongBitSet},
     * use the following loop:
     *
     *  <pre> {@code
     * for (int i = bs.length(); (i = bs.previousSetBit(i-1)) >= 0; ) {
     *     // operate on index i here
     * }}</pre>
     *
     * @param  fromIndex the index to start checking from (inclusive)
     * @return the index of the previous set bit, or {@code -1} if there
     *         is no such bit
     * @throws IndexOutOfBoundsException if the specified index is less
     *         than {@code -1}
     * @since  1.7
     */
    public long previousSetBit(long fromIndex) {
        if (fromIndex < 0) {
            if (fromIndex == -1)
                return -1;
            throw new IndexOutOfBoundsException(
                    "fromIndex < -1: " + fromIndex);
        }

        checkInvariants();

        int u = wordIndex(fromIndex);
        if (u >= wordsInUse)
            return length() - 1;

        long word = words[u] & (WORD_MASK >>> -(fromIndex+1));

        while (true) {
            if (word != 0)
                return (u+1) * BITS_PER_WORD - 1 - Long.numberOfLeadingZeros(word);
            if (u-- == 0)
                return -1;
            word = words[u];
        }
    }

    /**
     * Returns the index of the nearest bit that is set to {@code false}
     * that occurs on or before the specified starting index.
     * If no such bit exists, or if {@code -1} is given as the
     * starting index, then {@code -1} is returned.
     *
     * @param  fromIndex the index to start checking from (inclusive)
     * @return the index of the previous clear bit, or {@code -1} if there
     *         is no such bit
     * @throws IndexOutOfBoundsException if the specified index is less
     *         than {@code -1}
     * @since  1.7
     */
    public long previousClearBit(long fromIndex) {
        if (fromIndex < 0) {
            if (fromIndex == -1)
                return -1;
            throw new IndexOutOfBoundsException(
                    "fromIndex < -1: " + fromIndex);
        }

        checkInvariants();

        int u = wordIndex(fromIndex);
        if (u >= wordsInUse)
            return fromIndex;

        long word = ~words[u] & (WORD_MASK >>> -(fromIndex+1));

        while (true) {
            if (word != 0)
                return (u+1) * BITS_PER_WORD -1 - Long.numberOfLeadingZeros(word);
            if (u-- == 0)
                return -1;
            word = ~words[u];
        }
    }

    /**
     * Returns the "logical size" of this {@code LongBitSet}: the index of
     * the highest set bit in the {@code LongBitSet} plus one. Returns zero
     * if the {@code LongBitSet} contains no set bits.
     *
     * @return the logical size of this {@code LongBitSet}
     * @since  1.2
     */
    public long length() {
        if (wordsInUse == 0)
            return 0;

        return stickyLength != -1
                ? stickyLength
                : BITS_PER_WORD * (wordsInUse - 1) + (BITS_PER_WORD - Long.numberOfLeadingZeros(words[wordsInUse - 1]));
    }

    /**
     * Returns true if this {@code LongBitSet} contains no bits that are set
     * to {@code true}.
     *
     * @return boolean indicating whether this {@code LongBitSet} is empty
     * @since  1.4
     */
    public boolean isEmpty() {
        return wordsInUse == 0;
    }

    /**
     * Returns true if the specified {@code LongBitSet} has any bits set to
     * {@code true} that are also set to {@code true} in this {@code LongBitSet}.
     *
     * @param  set {@code LongBitSet} to intersect with
     * @return boolean indicating whether this {@code LongBitSet} intersects
     *         the specified {@code LongBitSet}
     * @since  1.4
     */
    public boolean intersects(LongBitSet set) {
        for (int i = Math.min(wordsInUse, set.wordsInUse) - 1; i >= 0; i--)
            if ((words[i] & set.words[i]) != 0)
                return true;
        return false;
    }

    /**
     * Returns the number of bits set to {@code true} in this {@code LongBitSet}.
     *
     * @return the number of bits set to {@code true} in this {@code LongBitSet}
     * @since  1.4
     */
    public long cardinality() {
        long sum = 0;
        for (int i = 0; i < wordsInUse; i++)
            sum += Long.bitCount(words[i]);
        return sum;
    }

    public long cardinalitySpace4ToString() {
        long sum = 0;
        for (int i = 0; i < wordsInUse; i++)
            // Count bits times number of digits to write the index number.
            sum += Long.bitCount(words[i]) * (Math.log10((long)i << ADDRESS_BITS_PER_WORD) + 1);

        return sum;
    }

    /**
     * Performs a logical <b>AND</b> of this target bit set with the
     * argument bit set. This bit set is modified so that each bit in it
     * has the value {@code true} if and only if it both initially
     * had the value {@code true} and the corresponding bit in the
     * bit set argument also had the value {@code true}.
     *
     * @param set a bit set
     */
    public void and(LongBitSet set) {
        if (this == set)
            return;

        while (wordsInUse > set.wordsInUse)
            words[--wordsInUse] = 0;

        // Perform logical AND on words in common
        for (int i = 0; i < wordsInUse; i++)
            words[i] &= set.words[i];

        recalculateWordsInUse();
        checkInvariants();
    }

    /**
     * Performs a logical <b>OR</b> of this bit set with the bit set
     * argument. This bit set is modified so that a bit in it has the
     * value {@code true} if and only if it either already had the
     * value {@code true} or the corresponding bit in the bit set
     * argument has the value {@code true}.
     *
     * @param set a bit set
     */
    public void or(LongBitSet set) {
        if (this == set)
            return;

        int wordsInCommon = Math.min(wordsInUse, set.wordsInUse);

        ensureCapacity(set);

        // Perform logical OR on words in common
        for (int i = 0; i < wordsInCommon; i++)
            words[i] |= set.words[i];

        // Copy any remaining words
        if (wordsInCommon < set.wordsInUse)
            System.arraycopy(set.words, wordsInCommon,
                    words, wordsInCommon,
                    wordsInUse - wordsInCommon);

        checkInvariants();
    }

    private void ensureCapacity(LongBitSet set) {
        if (wordsInUse < set.wordsInUse) {
            ensureCapacity(set.wordsInUse);
            wordsInUse = set.wordsInUse;
            if (sizeIsSticky) {
                stickyLength = set.stickyLength != -1 ? set.stickyLength : wordsInUse * BITS_PER_WORD;
            }
            invariantsMet = false;
        }
    }

    /**
     * Performs a logical <b>XOR</b> of this bit set with the bit set
     * argument. This bit set is modified so that a bit in it has the
     * value {@code true} if and only if one of the following
     * statements holds:
     * <ul>
     * <li>The bit initially has the value {@code true}, and the
     *     corresponding bit in the argument has the value {@code false}.
     * <li>The bit initially has the value {@code false}, and the
     *     corresponding bit in the argument has the value {@code true}.
     * </ul>
     *
     * @param  set a bit set
     */
    public void xor(LongBitSet set) {
        int wordsInCommon = Math.min(wordsInUse, set.wordsInUse);

        ensureCapacity(set);

        // Perform logical XOR on words in common
        for (int i = 0; i < wordsInCommon; i++)
            words[i] ^= set.words[i];

        // Copy any remaining words
        if (wordsInCommon < set.wordsInUse)
            System.arraycopy(set.words, wordsInCommon,
                    words, wordsInCommon,
                    set.wordsInUse - wordsInCommon);

        recalculateWordsInUse();
        checkInvariants();
    }

    /**
     * Clears all of the bits in this {@code LongBitSet} whose corresponding
     * bit is set in the specified {@code LongBitSet}.
     *
     * @param  set the {@code LongBitSet} with which to mask this
     *         {@code LongBitSet}
     * @since  1.2
     */
    public void andNot(LongBitSet set) {
        // Perform logical (a & !b) on words in common
        for (int i = Math.min(wordsInUse, set.wordsInUse) - 1; i >= 0; i--)
            words[i] &= ~set.words[i];

        recalculateWordsInUse();
        checkInvariants();
    }

    /**
     * Returns the hash code value for this bit set. The hash code depends
     * only on which bits are set within this {@code LongBitSet}.
     *
     * <p>The hash code is defined to be the result of the following
     * calculation:
     *  <pre> {@code
     * public int hashCode() {
     *     long h = 1234;
     *     long[] words = toLongArray();
     *     for (int i = words.length; --i >= 0; )
     *         h ^= words[i] * (i + 1);
     *     return (int)((h >> 32) ^ h);
     * }}</pre>
     * Note that the hash code changes if the set of bits is altered.
     *
     * @return the hash code value for this bit set
     */
    public int hashCode() {
        long h = 1234;
        for (int i = wordsInUse; --i >= 0; )
            h ^= words[i] * (i + 1);

        return (int)((h >> 32) ^ h);
    }

    /**
     * Returns the number of bits of space actually in use by this
     * {@code LongBitSet} to represent bit values.
     * The maximum element in the set is the size - 1st element.
     *
     * @return the number of bits currently in this bit set
     */
    public long size() {
        return (long) words.length * BITS_PER_WORD;
    }

    /**
     * Compares this object against the specified object.
     * The result is {@code true} if and only if the argument is
     * not {@code null} and is a {@code LongBitSet} object that has
     * exactly the same set of bits set to {@code true} as this bit
     * set. That is, for every nonnegative {@code int} index {@code k},
     * <pre>((LongBitSet)obj).get(k) == this.get(k)</pre>
     * must be true. The current sizes of the two bit sets are not compared.
     *
     * @param  obj the object to compare with
     * @return {@code true} if the objects are the same;
     *         {@code false} otherwise
     * @see    #size()
     */
    public boolean equals(Object obj) {
        if (!(obj instanceof LongBitSet))
            return false;
        if (this == obj)
            return true;

        LongBitSet set = (LongBitSet) obj;

        checkInvariants();
        set.checkInvariants();

        if (wordsInUse != set.wordsInUse)
            return false;

        // Check words in use by both LongBitSets
        for (int i = 0; i < wordsInUse; i++)
            if (words[i] != set.words[i])
                return false;

        return true;
    }

    /**
     * Cloning this {@code LongBitSet} produces a new {@code LongBitSet}
     * that is equal to it.
     * The clone of the bit set is another bit set that has exactly the
     * same bits set to {@code true} as this bit set.
     *
     * @return a clone of this bit set
     * @see    #size()
     */
    public Object clone() {
        if (! sizeIsSticky)
            trimToSize();

        try {
            LongBitSet result = (LongBitSet) super.clone();
            result.words = words.clone();
            result.checkInvariants();
            return result;
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e);
        }
    }

    /**
     * Attempts to reduce internal storage used for the bits in this bit set.
     * Calling this method may, but is not required to, affect the value
     * returned by a subsequent call to the {@link #size()} method.
     *
     * A call to this method could also mean an initially sizeIsSticky LongBitSet
     * now wants to be dynamic, disposing of unused zero bits.
     */
    private void trimToSize() {
        sizeIsSticky = false;
        stickyLength = -1;
        invariantsMet = false;
        recalculateWordsInUse();
        if (wordsInUse != words.length) {
            words = Arrays.copyOf(words, wordsInUse);
            checkInvariants();
        }
    }

    /**
     * Save the state of the {@code LongBitSet} instance to a stream (i.e.,
     * serialize it).
     */
    private void writeObject(ObjectOutputStream s)
            throws IOException {

        checkInvariants();

        if (! sizeIsSticky)
            trimToSize();

        ObjectOutputStream.PutField fields = s.putFields();
        fields.put("bits", words);
        fields.put("sizeIsSticky", sizeIsSticky);
        fields.put("stickyLength", stickyLength);
        fields.put("sizeIsSticky", sizeIsSticky);
        fields.put("wordsInUse", wordsInUse);
        s.writeFields();
    }

    /**
     * Reconstitute the {@code LongBitSet} instance from a stream (i.e.,
     * deserialize it).
     */
    private void readObject(ObjectInputStream s)
            throws IOException, ClassNotFoundException {

        ObjectInputStream.GetField fields = s.readFields();
        words = (long[]) fields.get("bits", null);
        sizeIsSticky = fields.get("sizeIsSticky", false);
        stickyLength = fields.get("stickyLength", -1L);
        invariantsMet = false;
        wordsInUse = fields.get("wordsInUse", words.length);
        checkInvariants();
    }

    /**
     * Returns a string representation of this bit set. For every index
     * for which this {@code LongBitSet} contains a bit in the set
     * state, the decimal representation of that index is included in
     * the result. Such indices are listed in order from lowest to
     * highest, separated by ",&nbsp;" (a comma and a space) and
     * surrounded by braces, resulting in the usual mathematical
     * notation for a set of integers.
     *
     * <p>Example:
     * <pre>
     * LongBitSet drPepper = new LongBitSet();</pre>
     * Now {@code drPepper.toString()} returns "{@code {}}".
     * <pre>
     * drPepper.set(2);</pre>
     * Now {@code drPepper.toString()} returns "{@code {2}}".
     * <pre>
     * drPepper.set(4);
     * drPepper.set(10);</pre>
     * Now {@code drPepper.toString()} returns "{@code {2, 4, 10}}".
     *
     * @return a string representation of this bit set
     */
    public String toString() {
        checkInvariants();
        // Could overflow when nbits > Integer.MAX_VALUE
        if (cardinalitySpace4ToString() > Integer.MAX_VALUE) {
            throw new UnsupportedOperationException(
                    "ToString not supported for LongBitSets representations larger than Integer.MAX_VALUE");
        }

        int numBits = (wordsInUse > 128) ?
                (int) cardinality() : wordsInUse * BITS_PER_WORD;
        StringBuilder b = new StringBuilder(6*numBits + 2);
        b.append('{');

        long i = nextSetBit(0);
        if (i != -1) {
            b.append(i);
            while (true) {
                if (++i < 0) break;
                if ((i = nextSetBit(i)) < 0) break;
                int endOfRun = (int) nextClearBit(i);
                do { b.append(", ").append(i); }
                while (++i != endOfRun);
            }
        }

        b.append('}');
        return b.toString();
    }

    /**
     * Returns a stream of indices for which this {@code LongBitSet}
     * contains a bit in the set state. The indices are returned
     * in order, from lowest to highest. The size of the stream
     * is the number of bits in the set state, equal to the value
     * returned by the {@link #cardinality()} method.
     *
     * <p>The bit set must remain constant during the execution of the
     * terminal stream operation.  Otherwise, the result of the terminal
     * stream operation is undefined.
     *
     * @return a stream of integers representing set indices
     * @since 1.8
     */
    public LongStream stream() {
        class LongBitSetIterator implements PrimitiveIterator.OfLong {
            long next = nextSetBit(0);

            @Override
            public boolean hasNext() {
                return next != -1;
            }

            @Override
            public long nextLong() {
                if (next != -1) {
                    long ret = next;
                    next = nextSetBit(next+1);
                    return ret;
                } else {
                    throw new NoSuchElementException();
                }
            }
        }

        return StreamSupport.longStream(
                () -> Spliterators.spliterator(
                        new LongBitSetIterator(), cardinality(),
                        Spliterator.ORDERED | Spliterator.DISTINCT | Spliterator.SORTED),
                Spliterator.SIZED | Spliterator.SUBSIZED |
                        Spliterator.ORDERED | Spliterator.DISTINCT | Spliterator.SORTED,
                false);
    }
}
