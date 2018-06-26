import { Channel, logWith } from './util';

export type WsPayload = string | Blob | ArrayBuffer;

export class WsChannel<A extends WsPayload> {
  private ws: WebSocket;
  private reader: Channel<A> = new Channel<A>();

  constructor(ws: WebSocket) {
    this.ws = ws;
    ws.onclose = (e) => this.onClose_(e);
    ws.onmessage = (e) => this.onMessage_(e);
    ws.onerror = (e) => {
      this.reader.close();
      logWith('WsChannel.read')(e);
    };
  }

  static async open<A extends WsPayload>(uri: string): Promise<WsChannel<A>> {
    const ws = new WebSocket(uri);
    await new Promise<void>((resolve, reject) => {
      ws.onopen = (e) => {
        resolve();
      };
      ws.onerror = (e) => {
        reject();
        logWith('OfferChannel.onError')(e);
      };
    });
    return new WsChannel<A>(ws);
  }

  onClose_(e: CloseEvent) {
    this.reader.close();
  }

  onMessage_(e: MessageEvent) {
    const data = e.data as A;
    this.reader.write(data);
  }

  read(): Promise<A> {
    return this.reader.read();
  }

  write(a: A) {
    this.ws.send(a);
  }
}

