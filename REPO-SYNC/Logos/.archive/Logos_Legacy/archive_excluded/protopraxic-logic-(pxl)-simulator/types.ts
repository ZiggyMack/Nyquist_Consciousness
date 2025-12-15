export interface PxlState {
  id_hold: boolean;
  nc_hold: boolean;
  em_hold: boolean;
}

export enum EpistemicLaw {
    ID = 'identity',
    NC = 'non_contradiction',
    EM = 'excluded_middle'
}

export enum OntologicalLaw {
    DI = 'distinction',
    RL = 'relation',
    AG = 'agency'
}

export interface Message {
  role: 'user' | 'model';
  text: string;
}

export interface LogEntry {
  message: string;
  status: 'pending' | 'success' | 'error' | 'neutral';
}
