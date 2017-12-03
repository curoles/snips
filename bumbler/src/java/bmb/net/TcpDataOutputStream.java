/** @file
  * @author    Igor Lesik 2016
  * @copyright Igor Lesik 2016
  *
  * @brief Extends java.io.DataOutputStream to prefix
  *        each chunk of data with 'size' byte that is common to Erlang.
  */
package bmb.net;

/** Extends java.io.DataOutputStream to prefix each chunk of data
  * with 'size' byte that is common to Erlang.
  *
  *
  */
public class TcpDataOutputStream extends java.io.DataOutputStream
{

    public
    TcpDataOutputStream(java.io.OutputStream out)
    {
        super(out);
    }

    /** Writes len bytes from the specified byte array starting at offset 'off'
      * to the underlying output stream. The writes are split in chunks of no
      * more than 2^8 bytes. Each chunk starts with a special byte that encodes
      * home many bytes in the following chunk.
      */
    public boolean writePacket(byte[] b, int off, int len)
    {
        assert (off + len < b.length);

        while (off < len) {
            int size = java.lang.Math.min(256, len - off);
            try {
                writeByte(size & 0xFF);
                write(b, off, size);
                flush();
            }
            catch (java.io.IOException e) {
                return false;
            }
            off += size;
            len -= size;
        }

        return true;
    }
}
