import { List } from 'immutable';

export class Channel<A> {
  private readers: List<(a: A) => void> = List.of<(a: A) => void>();
  private writers: List<A> = List.of<A>();
  private closedMark: any = {};
  private closed: boolean = false;

  close() {
    if (!this.closed) {
      this.closed = true;
      this.write(this.closedMark);
    }
  }

  async read(): Promise<A> {
    console.log('ch.read');
    if (this.writers.isEmpty()) {
      if (this.closed) {
        this.throwClosedError_();
      }

      return new Promise<A>((resolve) => {
        this.readers = this.readers.push(resolve);
      });
    } else {
      const res = this.writers.first();
      if (res === this.closedMark) {
        this.throwClosedError_();
      }

      this.writers = this.writers.shift();
      return res;
    }
  }

  write(a: A) {
    console.log('ch.write', a);
    if (this.closed) {
      console.log('ch.write, closed');
      this.throwClosedError_();
    }

    if (this.readers.isEmpty()) {
      console.log('ch.write, reader.isEmpty');
      this.writers = this.writers.push(a);
    } else {
      const k = this.readers.first();
      console.log('ch.write, reader.first', k);
      this.readers = this.readers.shift();
      k(a);
    }
  }

  private throwClosedError_() {
    throw new Error('Channel closed');
  }
}

export function logWith(tag?: string) {
  return (e?: any) => {
    console.log((tag || 'onError') + ':', e);
  };
}
