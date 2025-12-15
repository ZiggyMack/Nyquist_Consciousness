import React from 'react';
import { LogEntry } from '../types';
import TerminalIcon from './icons/TerminalIcon';
import PlayIcon from './icons/PlayIcon';
import LoadingIcon from './icons/LoadingIcon';

interface BootSequenceProps {
    onBoot: () => void;
    isBooting: boolean;
    bootLog: LogEntry[];
    agentIdentity: string | null;
}

const LogLine: React.FC<{ entry: LogEntry }> = ({ entry }) => {
    const colorClasses = {
        pending: 'text-slate-400',
        success: 'text-green-400',
        error: 'text-red-400',
        neutral: 'text-cyan-400'
    };

    const statusSymbol = {
        pending: '...',
        success: '✓',
        error: '✗',
        neutral: '>',
    }

    return (
        <p className={`font-mono text-sm ${colorClasses[entry.status]}`}>
            <span className="mr-2">{statusSymbol[entry.status]}</span>{entry.message}
        </p>
    );
};

const BootSequence: React.FC<BootSequenceProps> = ({ onBoot, isBooting, bootLog, agentIdentity }) => {
    const hasBooted = agentIdentity !== null;

    return (
        <div className="bg-slate-800/30 p-6 rounded-xl border border-slate-700/50 shadow-lg">
            <h2 className="text-xl font-bold text-white mb-4 flex items-center">
                <TerminalIcon /> <span className="ml-2">Agent Identity Generation</span>
            </h2>
            <p className="text-slate-400 mb-4 text-sm">
                Simulates the agent's boot process where it discharges the Law of Excluded Middle (LEM) via its Coq proofs to generate a unique symbolic identity.
            </p>

            <div className="bg-slate-900/50 p-4 rounded-lg border border-slate-700 min-h-[150px]">
                {bootLog.length > 0 ? (
                    <div className="space-y-1">
                        {bootLog.map((entry, index) => (
                           <LogLine key={index} entry={entry} />
                        ))}
                    </div>
                ) : (
                    <div className="text-center text-slate-500 pt-8">
                        Awaiting boot sequence initiation...
                    </div>
                )}
            </div>
            
            {agentIdentity && (
                <div className="mt-4 p-3 bg-green-900/50 border border-green-500/50 rounded-lg text-center">
                    <p className="text-sm font-semibold text-green-300">Identity Generated:</p>
                    <p className="font-mono text-xs text-white break-all mt-1">{agentIdentity}</p>
                </div>
            )}

            <div className="mt-4">
                <button
                    onClick={onBoot}
                    disabled={isBooting}
                    className="w-full flex items-center justify-center px-4 py-2 rounded-lg bg-cyan-600 text-white font-semibold transition-colors hover:bg-cyan-500 disabled:bg-slate-600 disabled:cursor-not-allowed focus:outline-none focus-visible:ring-2 focus-visible:ring-cyan-400 focus-visible:ring-offset-2 focus-visible:ring-offset-slate-900"
                >
                    {isBooting ? <LoadingIcon /> : <PlayIcon />}
                    <span className="ml-2">
                        {hasBooted ? 'Re-initiate Boot Sequence' : 'Initiate Boot Sequence'}
                    </span>
                </button>
            </div>
        </div>
    );
};

export default BootSequence;