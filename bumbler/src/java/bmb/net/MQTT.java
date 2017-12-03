/** @file
  * @author    Igor Lesik 2016
  * @copyright Igor Lesik 2016
  *
  * @brief MQTT constants and definitions.
  * 
  * @see http://docs.oasis-open.org/mqtt/mqtt/v3.1.1/os/mqtt-v3.1.1-os.html
  *
  *
  *
  */
package bmb.net;

public final class MQTT
{

    public enum CtrlPktType {
        RSV0((byte)0),
        CONNECT((byte)1),
        CONNACK((byte)2);

        byte type;
        CtrlPktType(byte t){type = t;}
    }


    /** Returns new byte array for Fixed Header + the rest */
    static
    byte[] newPacket(int pktLength) {
        
        int sizeEncLen = 0;
        int len = pktLength;
        do { sizeEncLen++; len /= 128;} while (len >0);
        byte[] bs = new byte[1 + sizeEncLen + pktLength];

        // encode Length
        len = pktLength;
        int i = 1;
        do {
            bs[i] = (byte)(len % 128);
            len = len / 128;
            // if there are more data to encode, set the top bit of this byte
            if ( len > 0 ) {bs[i] = (byte)(bs[i] | 0b10000000);}
            i++;
        } while ( len > 0 );

        return bs;
    }

    /** Makes Fixed Header */
    static
    byte[] newPacket_(
        byte ctrlPktType,
        byte ctrlPktFlags,
        int pktLength
    ){
        byte[] pkt = newPacket(pktLength);
        pkt[0] = (byte)(((ctrlPktType & 0xF) << 4) |
                     (ctrlPktFlags & 0xF)) /*& 0xFF*/;
        return pkt;
    }

    /** Makes Fixed Header */
    static
    byte[] newPacket(
        CtrlPktType ctrlPktType,
        byte ctrlPktFlags,
        int pktLength
    ){
        return newPacket_(ctrlPktType.type, ctrlPktFlags, pktLength);
    }

    /** New packet */
    static
    byte[] newPacket(
        CtrlPktType ctrlPktType,
        byte ctrlPktFlags,
        byte[] varHdr,
        byte[] payload
    ) {
        int pktLen = 0;
        if (varHdr != null) { pktLen += varHdr.length; }
        if (payload != null) { pktLen += payload.length; }

        byte[] pkt = newPacket(ctrlPktType, ctrlPktFlags, pktLen);
        int offset = pkt.length - pktLen;

        if (varHdr != null) {
            System.arraycopy(varHdr, 0, pkt, offset, varHdr.length);
            offset += varHdr.length;
        }

        if (payload != null) {
            System.arraycopy(payload, 0, pkt, offset, payload.length);
        }

        return pkt;
    }

    static
    byte[] newPktCONNECT()
    {
        byte[] vh = new byte[10];
        // Protocol Name
        vh[0] = 0;
        vh[1] = 4;
        vh[2] = 'M'; vh[3] = 'Q'; vh[4] = 'T'; vh[5] = 'T';
        // Protocol Level
        vh[6] = 4;
        // Connect Flags
        vh[7] = 0;
        // Keep Alive
        vh[8] = 0;
        vh[9] = 10;

        return newPacket(
            CtrlPktType.CONNECT,
            (byte)0b0000,
            vh,
            null
        );
    }
}
