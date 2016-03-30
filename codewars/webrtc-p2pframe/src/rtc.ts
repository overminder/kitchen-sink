import { WsChannel } from './ws';
import { logWith } from './util';

const kRtcConfig = {
  iceServers: [
    {urls: 'stun:stun.l.google.com:19302'}
  ]
};

export class RtcState {
  key: string;
  conn: RTCPeerConnection;
  ch: RTCDataChannel;
  offerCh: OfferChannel;

  static async bind(): Promise<RtcState> {
    const offerCh = await OfferChannel.open();
    const { conn, key, iceCandidates } = await mkConn(offerCh, true);
    const ch = mkChan(conn);

    await bind(conn, offerCh);
    for (const c of (await iceCandidates)) {
      writeCandidate(offerCh, c);
    }

    const thiz = new RtcState();
    thiz.key = key;
    thiz.conn = conn;
    thiz.offerCh = offerCh;
    thiz.ch = ch;
    return thiz;
  }

  static async connect(key: string): Promise<RtcState> {
    const offerCh = await OfferChannel.open();
    const { conn } = await mkConn(offerCh, false);
    const ch = await connect(conn, offerCh, key);

    const thiz = new RtcState();
    thiz.conn = conn;
    thiz.offerCh = offerCh;
    thiz.ch = ch;
    return thiz;
  }

  accept() {
    const openP = new Promise<void>((k, eb) => {
      this.ch.onopen = (e) => {
        console.log('accept, onOpen');
        k();
      };
      this.ch.onerror = eb;
    });
    return Promise.all([openP, accept(this.conn, this.offerCh)]);
  }
}

export class OfferChannel {
  private ws: WsChannel<string>;

  constructor(ws: WsChannel<string>) {
    this.ws = ws;
  }

  static async open(): Promise<OfferChannel> {
    const uri = 'ws://' + location.host + '/offer';
    return new OfferChannel(await WsChannel.open<string>(uri));
  }

  async read(): Promise<HasType> {
    return JSON.parse(await this.ws.read());
  }

  write<A extends HasType>(a: A) {
    this.ws.write(JSON.stringify(a));
  }
}

function attachLoggersToChan(ch: RTCDataChannel) {
  ch.onopen = logWith('sendCh.onOpen');
  ch.onclose = logWith('sendCh.onClose');
  ch.onerror = logWith('sendCh.onError');
  ch.onmessage = logWith('sendCh.onMessage');

  return ch;
}


export function mkChan(conn: RTCPeerConnection): RTCDataChannel {
  const rtcCh = conn.createDataChannel('dataCh', {
    ordered: true,
    protocol: 'sctp',
  });

  return attachLoggersToChan(rtcCh);
}

export async function mkConn(offerCh: OfferChannel, isServer: boolean = false) {
  // See https://webrtc.github.io/samples/src/content/datachannel/basic/js/main.js
  const conn = new RTCPeerConnection(kRtcConfig);

  let key: string;
  let iceCandidates: Promise<RTCIceCandidate[]>;
  if (isServer) {
    offerCh.write({
      type: 'allocKey'
    });
    const resp = await offerCh.read();
    key = (resp as KeyResponse).key;
    console.log('got key response', resp);

    iceCandidates = new Promise<RTCIceCandidate[]>((k) => {
      const cs: RTCIceCandidate[] = [];
      conn.onicecandidate = (e) => {
        console.log('onIceCandidate', e);
        const c = e.candidate;
        if (c == null) {
          console.log('Finished gathering Ice candidates.');
          k(cs);
        } else {
          console.log('Got an Ice candidate.', c);
          cs.push(c);
        }
      };
    });
  }
  else {
    conn.onicecandidate = (e) => {
      console.log('onIceCandidate, ignoring', e.candidate);
    };
  }

  conn.ondatachannel = logWith('conn.onDataChannel');
  conn.onstatechange = logWith('conn.onStateChange');
  conn.onopen = logWith('conn.onOpen');

  return { conn, key, iceCandidates };
}

export function writeCandidate(offerCh: OfferChannel, c: RTCIceCandidate) {
  offerCh.write({
    type: 'candidate',
    candidate: c,
  });
}


export async function bind(rtcConn: RTCPeerConnection, offerCh: OfferChannel) {
  const offer = await new Promise<RTCSessionDescription>((k, eb) => {
    rtcConn.createOffer(k, eb);
  });
  await new Promise<void>((k, eb) => rtcConn.setLocalDescription(offer, k, eb));
  console.log('createOffer ok', offer);
  offerCh.write(offer);
  while (true) {
    const msg = await offerCh.read();
    console.log('msg', msg);
    if (msg.type === 'offer-created') {
      console.log('offer-created');
      return;
    }
  }
}

export async function accept(rtcConn: RTCPeerConnection, offerCh: OfferChannel) {
  while (true) {
    console.log('accept loop');
    const msg = await offerCh.read();
    console.log('accept: msg', msg);
    if (msg.type === 'offer-accepted') {
      const resp = (msg as OfferAccepted).resp;
      return new Promise<void>((k, eb) => {
        rtcConn.setRemoteDescription(new RTCSessionDescription(resp), k, eb);
      });
    }
  }
}

interface ConnectRaceResult {
  isDataChannel: boolean;
  value: HasType | RTCDataChannel;
}

export async function connect(rtcConn: RTCPeerConnection,
                              offerCh: OfferChannel,
                              key: string) {
  offerCh.write({
    type: 'take-offer',
    key: key
  });

  let gotChannel = new Promise<ConnectRaceResult>((k) => {
    rtcConn.ondatachannel = (e: RTCDataChannelEvent) => {
      console.log('client.onDataChannel', e);
      k({
        isDataChannel: true,
        value: e.channel,
      });
    };
  });

  let msg: HasType;
  while (true) {
    // XXX: no way to put items back to the channel...
    const got = await Promise.race([gotChannel, offerCh.read().then((v) => ({
      isDataChannel: false,
      value: v,
    }))]);
    if (got.isDataChannel) {
      const ch = got.value as RTCDataChannel;
      return attachLoggersToChan(ch);
    } else {
      const msg = got.value as HasType;
      if (msg.type === 'offer') {
        const offer = new RTCSessionDescription(msg as RTCSessionDescriptionInit);
        await new Promise<void>((k, eb) => rtcConn.setRemoteDescription(offer, k, eb));
        const answer = await new Promise<RTCSessionDescription>((k, eb) => {
          rtcConn.createAnswer(k, eb);
        });
        console.log('createAnswer ok', answer);
        await new Promise<void>((k, eb) => rtcConn.setLocalDescription(answer, k, eb));
        console.log('setLocalDescription(answer) ok', answer);
        writeAnswer(offerCh, key, answer);
        console.log('writeAnswer ok', answer);

      } else if (msg.type === 'candidate') {
        await new Promise<void>((k, eb) => {
          rtcConn.addIceCandidate(new RTCIceCandidate((msg as CandidateResp).candidate), k, eb);
        });
      } else {
        console.warn('unknown message', msg);
      }
    }
  }
}

function writeAnswer(offerCh: OfferChannel, key: string, answer: RTCSessionDescription) {
  offerCh.write({
    'forKey': key,
    'type': answer.type,
    'sdp': answer.sdp,
  });
}

interface HasType {
  type?: string;
}

interface OfferCreated extends HasType {
  key: string;
}

interface OfferAccepted extends HasType {
  key: string;
  resp: RTCSessionDescriptionInit;
}

interface CandidateResp extends HasType {
  candidate: RTCIceCandidateInit;
}

interface KeyResponse {
  key: string;
}
