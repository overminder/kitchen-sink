// See https://webrtc.github.io/samples/src/content/datachannel/basic/js/main.js
const conn = new RTCPeerConnection(null);
const sendCh = conn.createDataChannel('sendCh');

console.log('rtc: ', conn);
console.log('ch: ', sendCh);

conn.onicecandidate = (e) => {
  console.log('onIceCandidate: ', e);
};

sendCh.onopen = (e) => {
  console.log('sendCh.onOpen', e);
};

sendCh.onclose = (e) => {
  console.log('sendCh.onClose', e);
};

const rconn = new RTCPeerConnection(null);
rconn.onicecandidate = (e) => console.log('rconn.onIceCandidate', e);
rconn.ondatachannel = (e) => {
  console.log('rconn.onDataChannel', e);
};

conn.createOffer((descr) => {
  console.log('createOffset ok', descr);
}, (e) => {
  console.log('createOffset error', e);
});
