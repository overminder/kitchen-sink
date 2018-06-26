import * as React from 'react';
import * as ReactDOM from 'react-dom';

import { Form } from './ui';

export function entryPoint(mountPoint: Element) {
  ReactDOM.render(<Form />, mountPoint);
}
